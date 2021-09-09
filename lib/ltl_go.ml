open Common
open Ast
open Containers

module G = struct
  include Graph.Persistent.Digraph.Concrete (struct
    type t = string

    let compare = String.compare

    let hash = Hashtbl.hash

    let equal = String.equal
  end)

  let find_vertices f g =
    let res = ref [] in
    iter_vertex (fun v -> if f v then res := v :: !res) g;
    !res

  let all_edges g =
    let res = ref [] in
    iter_edges_e (fun e -> res := e :: !res) g;
    !res
end

let template_ltl ~i ~prop_fns ~states ~initial_state ~prop_vars ~transitions ()
    =
  Format.sprintf
    {|
// LTL property %d

// Propositions
%s

type State%d int
const (
%s
)

type LTLMonitor%d struct {
  state     State%d
	succeeded bool
	failed    bool
  vars      map[string]map[string]bool
}

func NewLTLMonitor%d(vars map[string]map[string]bool) *LTLMonitor%d {
  return &LTLMonitor%d{
    vars: vars,
    state: %s,
    succeeded: false,
    failed: false,
  }
}

func (l *LTLMonitor%d) StepLTL%d(g Global) error {
	if l.succeeded {
		return nil
	} else if l.failed {
		return errors.New("property falsified")
	}


	// evaluate all the props
	%s

	// note the true ones, take that transition
	switch l.state {
	%s
	default:
		panic("invalid state")
	}
}
|}
    i prop_fns i states i i i i i initial_state i i prop_vars transitions

let template_monitor ~pname ~extra_imports ~global_contents ~action_defs
    ~preconditions ~postconditions ~ltl_monitor_defs ~ltl_monitor_fields
    ~ltl_monitor_assignments ~ltl_monitor_init ~ltl_monitor_step () =
  Format.sprintf
    {|
package rv%s

import (
	"errors"
  "fmt"
  "sync"
  "time"
  %s
)

type Global struct {
%s
}

type Action int
const (
%s
)

func all(s []string, f func(string) bool) bool {
	b := true
	for _, v := range s {
		b = b && f(v)
	}
	return b
}

func allSet(s map[string]bool, f func(string) bool) bool {
	b := true
	for k := range s {
		b = b && f(k)
	}
	return b
}

func any(s []string, f func(string) bool) bool {
	b := false
	for _, v := range s {
		b = b || f(v)
	}
	return b
}

func anySet(s map[string]bool, f func(string) bool) bool {
	b := false
	for k := range s {
		b = b || f(k)
	}
	return b
}

func (m *Monitor) precondition(g *Global, action Action, params ...string) error {
	switch action {
    %s
    default:
   		panic("invalid action")
	}
}

func (m *Monitor) applyPostcondition(action Action, params ...string) error {
	switch action {
    %s
    default:
   		panic("invalid action")
	}
  return nil
}

%s

type entry struct {
	action string
	params []string
}

type Log = []entry

type Monitor struct {
	previous Global
  PC map[string]int
  //vars     map[string][]string
  vars     map[string]map[string]bool
  %s
  Log Log
  ExecutionTimeNs int64
	lock        sync.Mutex
}

//func NewMonitor(vars map[string][]string) *Monitor {
func NewMonitor(vars map[string]map[string]bool) *Monitor {
	return &Monitor{
    // previous is the empty Global
    PC: map[string]int{}, // not the smae as a nil map
    vars: vars,
    %s
    // Everything else uses mzero
  }
}

func (m *Monitor) Reset() {
	m.lock.Lock()
	defer m.lock.Unlock()
	defer m.trackTime(time.Now())

	m.previous = Global{}
	m.PC = map[string]int{}
	// vars ok
  %s
	m.Log = Log{}

	// This is deliberately not reset, to track the total time the monitor has been used
	// m.ExecutionTimeNs = 0

	// lock ok
}

func (m *Monitor) Step(g Global, act Action, params ...string) error {
	m.lock.Lock()
	defer m.lock.Unlock()
  defer m.trackTime(time.Now())

	if err := m.precondition(&g, act, params...); err != nil {
    return err
	}

	m.previous = g

	if err := m.applyPostcondition(act, params...); err != nil {
    return err
  }

  // LTL monitors

  %s

  return nil
}

func (m *Monitor) StepA(act Action, params ...string) error {
	m.lock.Lock()
	defer m.lock.Unlock()
  defer m.trackTime(time.Now())

  if err := m.precondition(nil, act, params...); err != nil {
    return err
  }

  if err := m.applyPostcondition(act, params...); err != nil {
    return err
  }

  return nil
}

func (m *Monitor) StepS(g Global) error {
	m.lock.Lock()
	defer m.lock.Unlock()
  defer m.trackTime(time.Now())

  m.previous = g

  // LTL monitors

  %s

  return nil
}

func (m *Monitor) PrintLog() {
	m.lock.Lock()
	defer m.lock.Unlock()

	for _, e := range m.Log {
		fmt.Printf("%%s %%v\n", e.action, e.params)
	}
	// fmt.Printf("Monitor time taken: %%v\n", time.Duration(m.ExecutionTimeNs))
	fmt.Printf("Monitor time taken: %%d\n", m.ExecutionTimeNs)
}

func (m *Monitor) trackTime(start time.Time) {
    elapsed := time.Since(start)
    m.ExecutionTimeNs += elapsed.Nanoseconds()
}
|}
    pname extra_imports global_contents action_defs preconditions postconditions
    ltl_monitor_defs ltl_monitor_fields ltl_monitor_init ltl_monitor_assignments
    ltl_monitor_step ltl_monitor_step

let fresh =
  let n = ref 0 in
  fun () ->
    let r = !n in
    incr n;
    Format.sprintf "t%d" r

let rec extract_subexprs env (t : texpr) =
  match t.expr with
  (* TODO probably should distinguish temporal operators from bool here.  [] (a & b) vs ([] a & [] b) *)
  (* | App (("|" as f), args) *)
  (* | App (("&" as f), args) *)
  | App (("==>" as f), args) | App (("<>" as f), args) | App (("[]" as f), args)
    ->
    let sub = List.map (extract_subexprs env) args in
    let args1 = List.map fst sub in
    let maps = List.map snd sub in
    let res = { t with expr = App (f, args1) } in
    let merged_maps =
      List.fold_right
        (fun c t ->
          SMap.union (fun _ _ _ -> failwith "should not conflict") c t)
        maps SMap.empty
    in
    (res, merged_maps)
  | Else | Timeout -> nyi "else timeout"
  | App (_, _)
  | Int _ | Bool _ | String _ | Set _ | List _ | Map _ | Var _
  | Tuple (_, _) ->
    let v = fresh () in
    ({ t with expr = Var (V (None, v)) }, SMap.singleton v t)

let rec fml_to_ltl3tools (t : texpr) =
  match t.expr with
  | App ("[]", [t1]) -> Format.sprintf "[] (%s)" (fml_to_ltl3tools t1)
  | App ("<>", [t1]) -> Format.sprintf "<> (%s)" (fml_to_ltl3tools t1)
  | App ("==>", [a; b]) ->
    Format.sprintf "%s -> %s" (fml_to_ltl3tools a) (fml_to_ltl3tools b)
  | Var (V (_, v)) -> v
  | App (_, _) | Else | Timeout -> nyi "else/timeout"
  | Int _ | Bool _ | String _ | Set _ | List _ | Map _ | Tuple (_, _) ->
    bug "fml to ltl3 unexpected node"

let fml_ownership env (t : texpr) =
  let rec aux t =
    let own =
      match t.meta.info.own with
      | Global -> []
      | Party p -> [(IMap.find (UF.value p) env.parties).repr |> var_name]
    in
    own
    @
    match t.expr with
    | Set args | List args | App (_, args) -> List.concat_map aux args
    | Int _ | Bool _ | String _ | Var _ -> []
    | Else -> nyi "fml ownership else"
    | Timeout -> nyi "fml ownership timeout"
    | Map _ -> nyi "fml ownership tuple"
    | Tuple (_, _) -> nyi "fml ownership tuple"
  in
  aux t |> List.uniq ~eq:String.equal

let invoke_ltl2mon s =
  let res = CCUnix.call_full "ltl2mon '%s'" s in
  if res#errcode <> 0 then
    bad_input "unable to invoke ltl2mon"
  else
    (* Format.printf "error code %d@." res#errcode; *)
    (* Format.printf "stderr %s@." res#stderr; *)
    res#stdout

let debug = false

let invoke_gofmt s =
  (* TODO check if gofmt is present, and distinguish that from the case where we produce syntactically invalid Go code *)
  let res = CCUnix.call_full ~stdin:(`Str s) "gofmt" in
  if res#errcode = 0 then
    res#stdout
  else (
    if debug then print_endline res#stderr;
    s)

let parse_graphviz_output s =
  let edge_regex =
    Str.regexp {|"\([^"]+\)" -> "\([^"]+\)" \[label = "(\([^)]+\))"\]|}
  in
  let edges = ref [] in
  Str.global_substitute edge_regex
    (fun s ->
      edges :=
        ( Str.matched_group 1 s,
          Str.matched_group 2 s,
          Str.matched_group 3 s |> fun props ->
          match props with
          | "<empty>" -> SSet.empty
          | _ -> String.split ~by:"&&" props |> SSet.of_list )
        :: !edges;
      "")
    s
  |> ignore;
  let node_regex = Str.regexp {|"\([^"]+\)" \[.*color=\(.*\)\]|} in
  let nodes = ref [] in
  Str.global_substitute node_regex
    (fun s ->
      nodes := (Str.matched_group 1 s, Str.matched_group 2 s) :: !nodes;
      "")
    s
  |> ignore;
  (* rename the nodes *)
  let node_new_names =
    !nodes
    |> List.mapi (fun i (n, c) ->
           ( n,
             Format.sprintf "S_%d_%s" i
               (String.sub c 0 1 |> String.capitalize_ascii) ))
    |> SMap.of_list
  in
  let edges =
    !edges
    |> List.map (fun (f, t, s) ->
           (SMap.find f node_new_names, SMap.find t node_new_names, s))
  in
  let node_colours =
    !nodes
    |> List.map (fun (n, c) -> (SMap.find n node_new_names, c))
    |> SMap.of_list
  in
  (* compute some derived info *)
  let graph =
    G.empty
    |> List.fold_right
         (fun (_, n) g -> G.add_vertex g n)
         (node_new_names |> SMap.bindings)
    |> List.fold_right (fun (f, t, _) g -> G.add_edge_e g (f, t)) edges
  in
  (node_colours, edges, graph)

let%expect_test "parse_graphviz_output" =
  let output =
    {|
digraph G {
"(-1, 1)" -> "(-1, 1)" [label = "(<empty>)"];
"(-1, 1)" -> "(-1, 1)" [label = "(a&&b)"];
"(-1, 1)" -> "(-1, 1)" [label = "(a)"];
"(-1, 1)" -> "(-1, 1)" [label = "(b)"];
"(0, 0)" -> "(-1, 1)" [label = "(<empty>)"];
"(0, 0)" -> "(1, -1)" [label = "(a&&b)"];
"(0, 0)" -> "(0, 0)" [label = "(a)"];
"(0, 0)" -> "(1, -1)" [label = "(b)"];
"(1, -1)" -> "(1, -1)" [label = "(<empty>)"];
"(1, -1)" -> "(1, -1)" [label = "(a&&b)"];
"(1, -1)" -> "(1, -1)" [label = "(a)"];
"(1, -1)" -> "(1, -1)" [label = "(b)"];
"(1, -1)" [label="(1, -1)", style=filled, color=green]
"(0, 0)" [label="(0, 0)", style=filled, color=yellow]
"(-1, 1)" [label="(-1, 1)", style=filled, color=red]
}
|}
  in
  let (node_colors, edges, graph) = parse_graphviz_output output in
  Format.printf "%s@.%s@.%s@."
    ([%derive.show: string SMap.t] node_colors)
    ([%derive.show: (string * string * SSet.t) list] edges)
    ([%derive.show: (string * string) list] (G.all_edges graph));
  [%expect
    {|
    {"S_0_R" -> "red";"S_1_Y" -> "yellow";"S_2_G"
    -> "green"}
    [("S_2_G", "S_2_G", {b}); ("S_2_G", "S_2_G", {a});
      ("S_2_G", "S_2_G", {a, b}); ("S_2_G", "S_2_G", {});
      ("S_1_Y", "S_2_G", {b}); ("S_1_Y", "S_1_Y", {a});
      ("S_1_Y", "S_2_G", {a, b}); ("S_1_Y", "S_0_R", {});
      ("S_0_R", "S_0_R", {b}); ("S_0_R", "S_0_R", {a});
      ("S_0_R", "S_0_R", {a, b}); ("S_0_R", "S_0_R", {})]
    [("S_2_G", "S_2_G"); ("S_1_Y", "S_2_G"); ("S_1_Y", "S_1_Y");
      ("S_1_Y", "S_0_R"); ("S_0_R", "S_0_R")]
  |}]

let state_var_name s = snake_to_camel s

let rec compile_typ env t =
  match t with
  | TyParty _ ->
    (* how are parties represented? *)
    "string"
  | TySet t1 -> Format.sprintf "map[%s]bool" (compile_typ env t1)
  | TyList _ -> nyi "compile type list"
  | TyVar v -> compile_typ env (IMap.find (UF.value v) env.types)
  | TyInt -> "int"
  | TyBool -> "bool"
  | TyString -> "string"
  | TyFn (_, _) -> nyi "compile type fn"

let uses_reflect = ref false

let rec compile parties te =
  match te.expr with
  | Int i -> string_of_int i
  | Bool b -> string_of_bool b
  | String s -> Format.sprintf {|"%s"|} s
  | Set es ->
    let values =
      List.map (compile parties) es
      |> List.map (fun e -> Format.sprintf "\"%s\": bool," e)
      |> String.concat ""
    in
    Format.sprintf "map[string]bool{%s}" values
  | List _ -> nyi "compile list"
  | Map _ -> nyi "compile map"
  | App (f, args) ->
    let args = List.map (compile parties) args in
    if String.equal f "!=" then (
      uses_reflect := true;
      Format.sprintf "%s(%s)" "!reflect.DeepEqual" (String.concat ", " args))
    else if String.equal f "==" then (
      uses_reflect := true;
      Format.sprintf "%s(%s)" "reflect.DeepEqual" (String.concat ", " args))
    else if List.length args = 2 && not (is_alpha f.[0]) then
      let f1 = match f with "|" -> "||" | _ -> f in
      Format.sprintf "(%s %s %s)" (List.nth args 0) f1 (List.nth args 1)
    else
      let f1 = match f with "size" -> "len" | _ -> f in
      Format.sprintf "%s(%s)" f1 (String.concat ", " args)
  | Var (V (_, v)) when List.mem ~eq:String.equal v parties ->
    Format.sprintf "l.vars[\"%s\"]" (state_var_name v)
  | Var (V (_, v)) -> Format.sprintf "g.%s" (state_var_name v)
  | Tuple (_, _) -> nyi "compile tuple"
  | Else -> nyi "compile else"
  | Timeout -> nyi "compile timeout"

let check_monitorability env ltl node_colors =
  if
    SMap.bindings node_colors
    |> List.for_all (fun (_, c) -> String.equal "yellow" c)
  then
    bad_input "%a is not monitorable" (Print.pp_texpr ~env) ltl

let generate_ltl_monitor ltl_i env parties pname ltl =
  let (ltl1, bindings) = extract_subexprs env ltl in
  let fml = ltl1 |> fml_to_ltl3tools in
  let output = fml |> invoke_ltl2mon in
  if debug then (* TODO re-print the graphviz file with updated names? *)
    write_to_file ~filename:(Format.sprintf "ltl-%s-%d.dot" pname ltl_i) output;
  let (node_colors, edges, graph) = output |> parse_graphviz_output in
  check_monitorability env ltl node_colors;
  let initial_state =
    G.find_vertices
      (fun v ->
        G.in_degree graph v = 0
        || G.in_degree graph v = 1
           && List.mem ~eq:String.equal v (G.pred graph v))
      graph
    |> List.head_opt
    |> Option.get_exn_or "no initial state"
  in

  (* (node_colors, bindings, edges, initial_state) *)
  let states =
    match node_colors |> SMap.keys |> List.of_iter with
    | [] -> bad_input "states should not be empty"
    | n :: rest ->
      Format.sprintf "%s State%d = iota\n%s\n" n ltl_i
        (rest |> String.concat "\n")
  in
  let prop_vars =
    bindings |> SMap.bindings
    |> List.map (fun (v, _) ->
           if debug then
             Format.sprintf "%s := l.%s(g)\nprintln(\"%s\", %s)" v v v v
           else
             Format.sprintf "%s := l.%s(g)" v v)
    |> String.concat "\n"
  in
  let prop_fns =
    bindings |> SMap.bindings
    |> List.map (fun (v, te) ->
           Format.sprintf
             "func (l *LTLMonitor%d) %s(g Global) bool {\nreturn %s\n}" ltl_i v
             (compile parties te))
    |> String.concat "\n"
  in
  let generate_ifs eligible_edges vars props =
    let rec aux vars props =
      match vars with
      | [] ->
        (* find new state *)
        let new_state =
          match
            eligible_edges |> List.filter (fun (_, _, s) -> SSet.equal props s)
          with
          | [(_, t, _)] -> t
          | _ -> bug "could not find state"
        in
        let color = SMap.find new_state node_colors in
        let outcome =
          match color with
          | "green" -> {|l.succeeded = true
          return nil|}
          | "red" ->
            {|l.failed = true
          return errors.New("property falsified")|}
          | "yellow" -> "return nil"
          | _ -> bug "invalid color %s" color
        in
        Format.sprintf "l.state = %s\n%s" new_state outcome
      | v :: vs ->
        (* split on one of the propositions *)
        Format.sprintf
          {|if %s {
          %s
        } else {
          %s
        }|}
          v
          (aux vs (SSet.add v props))
          (aux vs props)
    in
    aux vars props
  in
  let transitions =
    node_colors |> SMap.keys |> List.of_iter
    |> List.map (fun n ->
           let eligible =
             edges |> List.filter (fun (f, _, _) -> String.equal f n)
           in
           Format.sprintf "case %s:\n%s" n
             (generate_ifs eligible
                (bindings |> SMap.keys |> List.of_iter)
                SSet.empty))
    |> String.concat "\n"
  in
  let type_name = Format.sprintf "LTLMonitor%d" ltl_i in
  let field_name = Format.sprintf "ltlMonitor%d" ltl_i in
  let fields = Format.sprintf "%s *%s" field_name type_name in
  let assignments =
    Format.sprintf "m.%s = NewLTLMonitor%d(m.vars)" field_name ltl_i
  in
  let inits = Format.sprintf "%s: NewLTLMonitor%d(vars)," field_name ltl_i in
  let steps =
    Format.sprintf
      {|if err := m.%s.StepLTL%d(g); err != nil {
    return err
  }|}
      field_name ltl_i
  in
  let defs =
    template_ltl ~i:ltl_i ~prop_fns ~states ~initial_state ~prop_vars
      ~transitions ()
  in
  (defs, fields, assignments, inits, steps)

let translate_party_ltl env ltl_i pname ltl tprotocol action_nodes parties =
  (* TODO use pname to qualify stuff *)
  let ltl_monitors =
    List.map (generate_ltl_monitor ltl_i env parties pname) ltl
  in
  let ltl_monitor_defs =
    ltl_monitors |> List.map (fun (d, _, _, _, _) -> d) |> String.concat "\n\n"
  in
  let ltl_monitor_fields =
    ltl_monitors |> List.map (fun (_, f, _, _, _) -> f) |> String.concat "\n"
  in
  let ltl_monitor_assignments =
    ltl_monitors |> List.map (fun (_, _, a, _, _) -> a) |> String.concat "\n"
  in
  let ltl_monitor_init =
    ltl_monitors |> List.map (fun (_, _, _, i, _) -> i) |> String.concat "\n"
  in
  let ltl_monitor_step =
    ltl_monitors |> List.map (fun (_, _, _, _, s) -> s) |> String.concat "\n"
  in
  let assigned = Actions.assigned_variables tprotocol in

  let pc = "PC" in
  (* start filling in the template *)
  let tid_to_string bound (t : tid) =
    match t.params with
    | [] -> t.name
    | _ ->
      Format.sprintf "\"%s_\" + (%s)" t.name
        (List.mapi
           (fun i (v, s) ->
             if List.mem_assoc ~eq:String.equal v bound then
               Format.sprintf "%s" v
             else
               Format.sprintf "params[%d] /* %s : %s */" i v s)
           t.params
        |> String.concat "+")
  in
  let params_check params =
    match params with
    | [] -> ""
    | _ ->
      let l = List.length params in
      Format.sprintf
        {|if len(params) != %d { return errors.New("expected %d params") }|} l l
  in
  let preconditions =
    let open Actions in
    let fence_to_precondition act (f : fence_cond) =
      let rec aux bound f =
        match f with
        | ThreadStart ->
          let current_tid = act.protocol.pmeta.tid in
          Format.sprintf "m.%s[%s] == %d" pc
            (tid_to_string bound current_tid)
            default_pc_value
        | AnyOf fs -> List.map (aux bound) fs |> String.concat " || "
        | AllOf fs -> List.map (aux bound) fs |> String.concat " && "
        | Forall (v, s, z) ->
          Format.sprintf
            "allSet(m.vars[\"%s\"], func(%s string) bool { return %s })" s v
            (aux ((v, s) :: bound) z)
        | Cond (tid, i) ->
          Format.sprintf "m.%s[%s] == %d" pc (tid_to_string bound tid) i
      in
      aux [] f
    in
    IMap.bindings action_nodes
    |> List.map (fun (id, act) ->
           let name = Actions.node_name pname (id, act) in
           let pres =
             match act.preconditions with
             | [] -> "// no preconditions"
             | _ ->
               act.preconditions
               |> List.map (fun p ->
                      Format.sprintf
                        {|if g != nil && !(%s) {
              return fmt.Errorf("logical precondition of %%s, %%v violated", "%s", params)
            }|}
                        (compile parties p) name)
               |> String.concat "\n"
           in
           let body =
             Format.sprintf
               {|%s
               %s
               if ! (%s) {
                 return fmt.Errorf("control precondition of %s %%v violated", params)
               }
               m.Log = append(m.Log, entry{action: "%s", params: params})
               return nil|}
               (params_check act.params) pres
               (fence_to_precondition act act.fence)
               name name
           in
           Format.sprintf "case %s:\n%s" name body)
    |> String.concat "\n"
  in
  let postconditions =
    let open Actions in
    IMap.bindings action_nodes
    |> List.map (fun (id, act) ->
           let tid = act.protocol.pmeta.tid in
           Format.sprintf
             {|case %s:
           %s
           m.%s[%s] = %d|}
             (Actions.node_name pname (id, act))
             (params_check act.params) pc (tid_to_string [] tid) id)
    |> String.concat "\n"
  in
  let action_defs =
    match IMap.bindings action_nodes with
    | [] -> bug "no actions"
    | (id, act) :: rest ->
      Format.sprintf "%s Action = iota\n%s"
        (Actions.node_name pname (id, act))
        (rest
        |> List.map (fun (id1, act1) -> Actions.node_name pname (id1, act1))
        |> String.concat "\n")
  in
  let global_contents =
    assigned
    |> List.map (fun (v, info) ->
           Format.sprintf "%s %s" (state_var_name v) (compile_typ env info.typ))
    |> String.concat "\n"
  in
  let extra_imports = if !uses_reflect then "\"reflect\"" else "" in
  template_monitor
    ~pname:(String.lowercase_ascii pname)
    ~extra_imports ~global_contents ~action_defs ~preconditions ~postconditions
    ~ltl_monitor_defs ~ltl_monitor_fields ~ltl_monitor_assignments
    ~ltl_monitor_init ~ltl_monitor_step ()

let translate_party_ltl env i pname ltl tprotocol action_nodes parties =
  if not (IMap.is_empty action_nodes) then
    let code =
      translate_party_ltl env i pname ltl tprotocol action_nodes parties
      |> invoke_gofmt
    in
    write_to_file ~filename:(Format.sprintf "monitor%s.go" pname) code
