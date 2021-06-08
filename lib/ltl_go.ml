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

let template ~extra_imports ~global_contents ~prop_fns ~states ~action_defs
    ~preconditions ~postconditions ~initial_state ~prop_vars ~transitions () =
  Format.sprintf
    {|
package rv

import (
	"errors"
  %s
)

type Global struct {
%s
}

%s

type State int
const (
%s
)

type Action int
const (
%s
)

func (m *Monitor) precondition(action Action) bool {
	switch action {
    %s
    default:
   		panic("invalid action")
	}
}

func (m *Monitor) applyPostcondition(action Action) {
	switch action {
    %s
    default:
   		panic("invalid action")
	}
}

type Monitor struct {
	state    State
	previous Global
	done     bool
	dead     bool
  pc       int
  vars     map[string]interface{}
}

func NewMonitor(vars map[string]interface{}) *Monitor {
	return &Monitor{
    state: %s,
    // previous is the empty Global
    done: false,
    dead: false,
    pc: -1,
    vars: vars,
  }
}

// For debugging
func (m *Monitor) InternalState() State {
	return m.state
}

func (m *Monitor) Step(g Global, act Action) error {
	if m.done {
		return nil
	} else if m.dead {
		return errors.New("sink state")
	}

	if !m.precondition(act) {
		return errors.New("precondition violation")
	}

	m.previous = g

	m.applyPostcondition(act)

	// evaluate all the props
	%s

	// note the true ones, take that transition
	switch m.state {
	%s
	default:
		panic("invalid state")
	}
}
|}
    extra_imports global_contents prop_fns states action_defs preconditions
    postconditions initial_state prop_vars transitions

let fresh =
  let n = ref 0 in
  fun () ->
    let r = !n in
    incr n;
    Format.sprintf "t%d" r

let rec extract_subexprs (t : texpr) =
  match t.expr with
  (* TODO probably should distinguish temporal operators from bool here.  [] (a & b) vs ([] a & [] b) *)
  (* | App (("|" as f), args) *)
  (* | App (("&" as f), args) *)
  | App (("==>" as f), args) | App (("<>" as f), args) | App (("[]" as f), args)
    ->
    let sub = List.map extract_subexprs args in
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
  | App (_, _) | Int _ | Bool _ | Set _ | List _ | Map _ | Var _ | Tuple (_, _)
    ->
    let v = fresh () in
    ({ t with expr = Var (V (None, v)) }, SMap.singleton v t)

let rec fml_to_ltl3tools (t : texpr) =
  match t.expr with
  | App ("[]", [t1]) -> Format.sprintf "[] (%s)" (fml_to_ltl3tools t1)
  | App ("<>", [t1]) -> Format.sprintf "<> (%s)" (fml_to_ltl3tools t1)
  | App ("==>", [a; b]) ->
    Format.sprintf "%s ==> %s" (fml_to_ltl3tools a) (fml_to_ltl3tools b)
  | Var (V (_, v)) -> v
  | App (_, _) | Int _ | Bool _ | Set _ | List _ | Map _ | Tuple (_, _) ->
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
    | Int _ | Bool _ | Var _ -> []
    | Map _ -> nyi "fml ownership tuple"
    | Tuple (_, _) -> nyi "fml ownership tuple"
  in
  aux t |> List.uniq ~eq:String.equal

let invoke_ltl2mon s =
  let res = CCUnix.call_full "ltl2mon '%s'" s in
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
    {S_0_R -> "red";S_1_Y -> "yellow";S_2_G
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

let state_var_name s = String.capitalize_ascii s

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
  | TyFn (_, _) -> nyi "compile type fn"

let uses_reflect = ref false

let rec compile parties te =
  match te.expr with
  | Int i -> string_of_int i
  | Bool b -> string_of_bool b
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
      let f1 = match f with "size" -> "Len" | _ -> f in
      Format.sprintf "%s(%s)" f1 (String.concat ", " args)
  | Var (V (_, v)) when List.mem ~eq:String.equal v parties ->
    Format.sprintf "m.vars[\"%s\"]" (state_var_name v)
  | Var (V (_, v)) -> Format.sprintf "g.%s" (state_var_name v)
  | Tuple (_, _) -> nyi "compile tuple"

let check_monitorability env ltl node_colors =
  if
    SMap.bindings node_colors
    |> List.for_all (fun (_, c) -> String.equal "yellow" c)
  then
    bad_input "%a is not monitorable" (Print.pp_texpr ~env) ltl

let translate_party_ltl env ltl_i (pname, ltl) tprotocol action_graph
    action_nodes parties =
  (* TODO use ltl_i when having multiple properties falsified is supported *)
  (* TODO use pname to qualify stuff *)
  let fmls =
    ltl
    |> List.map (fun ltl ->
           let (ltl1, bindings) = extract_subexprs ltl in
           let fml = ltl1 |> fml_to_ltl3tools in
           let output = fml |> invoke_ltl2mon in
           if debug then
             (* TODO re-print the graphviz file with updated names? *)
             write_to_file
               ~filename:(Format.sprintf "ltl-%s-%d.dot" pname ltl_i)
               output;
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
           (node_colors, bindings, edges, initial_state))
  in
  let node_colors = List.map (fun (a, _, _, _) -> a) fmls in
  let bindings = List.map (fun (_, a, _, _) -> a) fmls in
  let edges = List.map (fun (_, _, a, _) -> a) fmls in
  let initial_state = List.map (fun (_, _, _, a) -> a) fmls in

  (* TODO support generating more than one automaton, need to eliminate the return in the state machine transitions *)
  let node_colors = List.hd node_colors in
  let bindings = List.hd bindings in
  let edges = List.hd edges in
  let initial_state = List.hd initial_state in

  let assigned = Actions.assigned_variables tprotocol in

  (* start filling in the template *)
  let preconditions =
    IMap.bindings action_nodes
    |> List.map (fun (id, act) ->
           let preds = Actions.G.pred action_graph id in
           let body =
             match preds with
             | [] -> Format.sprintf "return true"
             | _ ->
               Format.sprintf "return %s"
                 (List.map (fun p -> Format.sprintf "m.pc == %d" p) preds
                 |> String.concat " || ")
           in
           Format.sprintf "case %s:\n%s"
             (Actions.node_name pname (id, act))
             body)
    |> String.concat "\n"
  in
  let postconditions =
    IMap.bindings action_nodes
    |> List.map (fun (id, act) ->
           Format.sprintf "case %s:\nm.pc = %d"
             (Actions.node_name pname (id, act))
             id)
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
  let states =
    match node_colors |> SMap.keys |> List.of_iter with
    | [] -> bad_input "states should not be empty"
    | n :: rest ->
      Format.sprintf "%s State = iota\n%s\n" n (rest |> String.concat "\n")
  in
  let prop_vars =
    bindings |> SMap.bindings
    |> List.map (fun (v, _) ->
           if debug then
             Format.sprintf "%s := m.%s(g)\nprintln(\"%s\", %s)" v v v v
           else
             Format.sprintf "%s := m.%s(g)" v v)
    |> String.concat "\n"
  in
  let prop_fns =
    bindings |> SMap.bindings
    |> List.map (fun (v, te) ->
           Format.sprintf "func (m *Monitor) %s(g Global) bool {\nreturn %s\n}"
             v (compile parties te))
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
          | "green" -> "m.done = true\nreturn nil"
          | "red" -> "m.dead = true\nreturn errors.New(\"sink state\")"
          | "yellow" -> "return nil"
          | _ -> bug "invalid color %s" color
        in
        Format.sprintf "m.state = %s\n%s" new_state outcome
      | v :: vs ->
        (* split on one of the propositions *)
        Format.sprintf "if %s {\n%s\n} else {\n%s\n}\n" v
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
  let extra_imports = if !uses_reflect then "\"reflect\"" else "" in
  template ~extra_imports ~global_contents ~prop_fns ~states ~action_defs
    ~preconditions ~postconditions ~initial_state ~prop_vars ~transitions ()

let translate_party_ltl env _ltl_i (pname, ltl) tprotocol action_graph
    action_nodes parties =
  let code =
    translate_party_ltl env _ltl_i (pname, ltl) tprotocol action_graph
      action_nodes parties
    |> invoke_gofmt
  in
  write_to_file ~filename:(Format.sprintf "monitor%s.go" pname) code
