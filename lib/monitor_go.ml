open Common
open Ast
open Containers

open Log.Make (struct
  let name = "monitor"
end)

type flags = {
  mutable uses_reflect : bool;
  mutable uses_errors : bool;
  mutable declared_types : (string * string) list;
  mutable fresh_local : int;
}

type go_expr = string list * string

let initial_flags =
  {
    uses_reflect = false;
    uses_errors = false;
    declared_types = [];
    fresh_local = 0;
  }

(* copy, we can't share the mutable object *)
let flags =
  {
    uses_reflect = false;
    uses_errors = false;
    declared_types = [];
    fresh_local = 0;
  }

let restore_flags () =
  flags.uses_reflect <- initial_flags.uses_reflect;
  flags.uses_errors <- initial_flags.uses_errors;
  flags.declared_types <- initial_flags.declared_types

let declare_type record_name field_types =
  if
    Option.is_none
      (List.assoc_opt ~eq:String.equal record_name flags.declared_types)
  then
    flags.declared_types <- (record_name, field_types) :: flags.declared_types

let fresh_variable () =
  let r = flags.fresh_local in
  flags.fresh_local <- flags.fresh_local + 1;
  Format.sprintf "v%d" r

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
  let i = string_of_int i in
  [%string
    {|
// LTL property %{i}

// Propositions
%{prop_fns}

type State%{i} int
const (
%{states}
)

type LTLMonitor%{i} struct {
	state     State%{i}
	succeeded bool
	failed    bool
	vars      map[string]interface{}
}

func NewLTLMonitor%{i}(vars map[string]interface{}) *LTLMonitor%{i} {
	return &LTLMonitor%{i}{
		vars: vars,
		state: %{initial_state},
		succeeded: false,
		failed: false,
	}
}

func (l *LTLMonitor%{i}) StepLTL%{i}(g Global) error {
	if l.succeeded {
		return nil
	} else if l.failed {
		return errors.New("property falsified")
	}

	// evaluate all the props
	%{prop_vars}

	// note the true ones, take that transition
	switch l.state {
	%{transitions}
	default:
		panic("invalid state")
	}
}
|}]

let template_monitor ~pname ~extra_imports ~global_contents ~action_defs
    ~preconditions ~postconditions ~ltl_monitor_defs ~ltl_monitor_fields
    ~ltl_monitor_assignments ~ltl_monitor_init ~ltl_monitor_step
    ~protocol_effects ~declared_types () =
  [%string
    {|package rv%{pname}

import (
	"fmt"
	"sync"
	"time"
  "reflect"
	%{extra_imports}
)

// The type of abstract state which the user must construct via a refinement mapping. We also maintain a copy of this to compare against.
type Global struct {
%{global_contents}
}

%{declared_types}

var state = Global{
  // initialize
}

type Action int
const (
%{action_defs}
)

var None = map[string]string{}

func allSlice(s []string, f func(string) bool) bool {
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

func anySlice(s []string, f func(string) bool) bool {
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

func (m *Monitor) precondition(g *Global, action Action, cparams map[string]string, lparams map[string]string) error {
	switch action {
		%{preconditions}
		default:
			panic("invalid action")
	}
}

func (m *Monitor) applyProtocolEffect(g *Global, action Action, lparams map[string]string) error {
	switch action {
		%{protocol_effects}
		default:
			panic("invalid action")
	}
}

func (m *Monitor) applyControlPostcondition(action Action, cparams map[string]string) error {
	switch action {
		%{postconditions}
		default:
			panic("invalid action")
	}
	return nil
}

%{ltl_monitor_defs}

type entry struct {
	action string
	cparams map[string]string
	lparams map[string]string
}

type Log = []entry

type Monitor struct {
	g Global
	PC map[string]int
	vars     map[string]interface{}
	%{ltl_monitor_fields}
	Log Log
	ExecutionTimeNs int64
	lock        sync.Mutex
}
// vars is a list of parameters provided at runtime, such as the concrete
// identifiers of the members of a party set, and the identifier to use for
// `self`.
func NewMonitor(vars map[string]interface{}) *Monitor {
	return &Monitor{
    // g is the empty Global. initialization is done by users as part of protocols
    PC: map[string]int{}, // not the same as a nil map
    vars: vars,
		%{ltl_monitor_init}
    // Everything else uses mzero
  }
}

// deprecated, as loops should be part of protocols
func (m *Monitor) Reset() {
	m.lock.Lock()
	defer m.lock.Unlock()
	defer m.trackTime(time.Now())

	m.PC = map[string]int{}
	// vars ok
  %{ltl_monitor_assignments}
	m.Log = Log{}

	// This is deliberately not reset, to track the total time the monitor has been used
	// m.ExecutionTimeNs = 0

	// lock ok
}

// A for Action. Given an action and its parameters, performs a transition.
func (m *Monitor) StepA(act Action, cparams map[string]string) error {
	m.lock.Lock()
	defer m.lock.Unlock()
	defer m.trackTime(time.Now())

	if err := m.precondition(nil, act, cparams, map[string]string{}); err != nil {
		return err
	}

	if err := m.applyControlPostcondition(act, cparams); err != nil {
		return err
	}

  m.Log = append(m.Log, entry{action: fmt.Sprintf("%v", act), cparams: cparams, lparams: map[string]string{}})

	return nil
}

// S for State. Checks that given abstract state is allowed.
func (m *Monitor) StepS(g Global) error {
	m.lock.Lock()
	defer m.lock.Unlock()
	defer m.trackTime(time.Now())

	// LTL monitors

	%{ltl_monitor_step}

	return nil
}

// Combination of StepA and StepS
func (m *Monitor) Step(g1 Global, act Action, cparams map[string]string, lparams map[string]string) error {
	m.lock.Lock()
	defer m.lock.Unlock()
	defer m.trackTime(time.Now())

	if err := m.precondition(&m.g, act, cparams, lparams); err != nil {
		return err
	}

  if err := m.applyProtocolEffect(&m.g, act, lparams); err != nil {
    return err
  }

  if !reflect.DeepEqual(m.g, g1) {
    return fmt.Errorf("postcondition violation: abstract states were not equal\nexpected: %#v\nreceived: %#v", m.g, g1)
  }

	if err := m.applyControlPostcondition(act, cparams); err != nil {
		return err
	}

  m.Log = append(m.Log, entry{action: fmt.Sprintf("%v", act), cparams: cparams, lparams: lparams})

	// LTL monitors

	%{ltl_monitor_step}

	return nil
}

func (m *Monitor) PrintLog() {
	m.lock.Lock()
	defer m.lock.Unlock()

	for _, e := range m.Log {
		fmt.Printf("%s %#v %#v\n", e.action, e.cparams, e.lparams)
	}
	// fmt.Printf("Monitor time taken: %#v\n", time.Duration(m.ExecutionTimeNs))
	fmt.Printf("Monitor time taken: %d\n", m.ExecutionTimeNs)
}

func (m *Monitor) trackTime(start time.Time) {
	elapsed := time.Since(start)
	m.ExecutionTimeNs += elapsed.Nanoseconds()
}
|}]

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
  | App (_, _)
  | Int _ | Bool _ | String _ | Set _ | List _ | Map _ | MapComp _ | MapProj _
  | Ite _ | Let _ | Var _ | Record _ ->
    let v = fresh () in
    ({ t with expr = Var (V (None, v)) }, SMap.singleton v t)

let rec fml_to_ltl3tools (t : texpr) =
  match t.expr with
  | App ("[]", [t1]) -> Format.sprintf "[] (%s)" (fml_to_ltl3tools t1)
  | App ("<>", [t1]) -> Format.sprintf "<> (%s)" (fml_to_ltl3tools t1)
  | App ("==>", [a; b]) ->
    Format.sprintf "%s -> %s" (fml_to_ltl3tools a) (fml_to_ltl3tools b)
  | Var (V (_, v)) -> v
  | App (_, _) -> nyi "app"
  | Int _ | Bool _ | String _ | Set _ | List _ | Map _ | MapComp _ | MapProj _
  | Ite _ | Let _ | Record _ ->
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
    | Ite _ -> nyi "fml ownership ite"
    | Map _ -> nyi "fml ownership map"
    | MapComp _ -> nyi "fml ownership map comp"
    | MapProj _ -> nyi "fml ownership map proj"
    | Let _ -> nyi "fml ownership let"
    | Record _ -> nyi "fml ownership record"
  in
  aux t |> List.uniq ~eq:String.equal

let invoke_ltl2mon s =
  let res = CCUnix.call_full "ltl2mon '%s'" s in
  if res#errcode <> 0 then bad_input "unable to invoke ltl2mon"
  else
    (* Format.printf "error code %d@." res#errcode; *)
    (* Format.printf "stderr %s@." res#stderr; *)
    res#stdout

let debug = true

let invoke_gofmt s =
  (* TODO check if gofmt is present, and distinguish that from the case where we produce syntactically invalid Go code *)
  let res = CCUnix.call_full ~stdin:(`Str s) "gofmt" in
  if res#errcode = 0 then begin
    log "gofmt succeeded";
    res#stdout
  end
  else (
    if debug then log "gofmt failed: %s" res#stderr;
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
  let node_colors, edges, graph = parse_graphviz_output output in
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

let record_name_of kvs =
  kvs |> List.map fst |> List.sort_uniq ~cmp:String.compare |> String.concat "_"

let rec compile_typ env t =
  match t with
  | TyParty _ ->
    (* how are parties represented? *)
    "string"
  | TyVar v -> compile_typ env (IMap.find (UF.value v) env.types)
  | TyInt -> "int"
  | TyBool -> "bool"
  | TyString -> "string"
  (* generate slices *)
  | TyMap (TyInt, v) -> Format.asprintf "[]%s" (compile_typ env v)
  (* sets are maps *)
  | TyMap (k, TyBool) -> Format.asprintf "map[%s]bool" (compile_typ env k)
  (* regular maps *)
  | TyMap (k, v) ->
    Format.asprintf "map[%s]%s" (compile_typ env k) (compile_typ env v)
  | TyFn (_, _) -> nyi "compile type fn" (* seems hard *)
  | TyRecord kvs ->
    let record_name = record_name_of kvs in
    snake_to_camel record_name

module List = struct
  include List

  let rec split3 (xs : ('a * 'b * 'c) list) : 'a list * 'b list * 'c list =
    match xs with
    | [] -> ([], [], [])
    | (a, b, c) :: rest ->
      let as_, bs, cs = split3 rest in
      (a :: as_, b :: bs, c :: cs)
end

let check_param_key l k =
  [
    Format.asprintf "if _, ok := %sparams[\"%s\"]; !ok {" l k;
    Format.asprintf
      "return fmt.Errorf(\"expected %s to be in %sparams: %%v\", %sparams)" k l
      l;
    "}";
  ]

let check_lparam_key k = check_param_key "l" k
let check_cparam_key k = check_param_key "c" k

let compile_expr :
    (string * party_set) list ->
    env ->
    string list ->
    texpr ->
    string list * string * string list =
  let bound = ref [] in
  fun params env parties te ->
    let rec comp : texpr -> string list * string * string list =
     fun te ->
      match te.expr with
      | Int i -> ([], string_of_int i, [])
      | Bool b -> ([], string_of_bool b, [])
      | String s -> ([], Format.sprintf {|"%s"|} s, [])
      | Set es ->
        let stmts, values, lparams = List.map comp es |> List.split3 in
        let contents =
          values
          |> List.map (fun e -> Format.sprintf "%s: true," e)
          |> String.concat ""
        in
        let typ =
          match Infer.concretize env te.meta.info.typ with
          | TyMap (a, TyBool) -> compile_typ env a
          | _ -> bug "cannot treat as set type"
        in
        ( List.concat stmts,
          Format.sprintf "map[%s]bool{%s}" typ contents,
          List.concat lparams )
      | List xs ->
        let typ =
          match Infer.concretize env te.meta.info.typ with
          | TyMap (TyInt, a) -> compile_typ env a
          | _ -> bug "cannot treat as list type"
        in
        let stmts, contents, lparams = List.map comp xs |> List.split3 in
        let list_literal = true in
        begin
          match list_literal with
          | true ->
            let contents = contents |> String.concat ", " in
            ( List.concat stmts,
              Format.sprintf "[]%s{%s}" typ contents,
              List.concat lparams )
          | false ->
            (* compile to a map literal... *)
            let contents =
              List.mapi (fun i c -> Format.sprintf "%d: %s" i c) contents
              |> String.concat ", "
            in
            ( List.concat stmts,
              Format.sprintf "map[int]%s{%s}" typ contents,
              List.concat lparams )
        end
      | Map kvs ->
        let k_typ, v_typ =
          match Infer.concretize env te.meta.info.typ with
          | TyMap (k, v) -> (compile_typ env k, compile_typ env v)
          | _ -> bug "cannot treat this type as map"
        in
        let stmts, contents, lparams =
          List.map
            (fun (k, v) ->
              let sv, v, lp = comp v in
              (sv, (k, v), lp))
            kvs
          |> List.split3
        in
        let contents =
          contents
          |> List.map (fun (k, v) -> Format.sprintf "\"%s\": %s" k v)
          |> String.concat ", "
        in
        ( List.concat stmts,
          Format.sprintf "map[%s]%s{%s}" k_typ v_typ contents,
          List.concat lparams )
      | Ite (c, e1, e2) ->
        let sc, c, lpc = comp c in
        let se, e1, lpe1 = comp e1 in
        let se1, e2, lpe2 = comp e2 in
        let v = fresh_variable () in
        let ite =
          [
            "// ite";
            Format.sprintf "var %s %s" v
              (compile_typ env (Infer.concretize env te.meta.info.typ));
            Format.sprintf "if %s {" c;
            Format.sprintf "%s = %s" v e1;
            "} else {";
            Format.sprintf "%s = %s" v e2;
            "}";
          ]
        in
        (List.concat [sc; se; se1; ite], v, lpc @ lpe1 @ lpe2)
      | MapComp mc ->
        let tk =
          compile_typ env (Infer.concretize env mc.map_key.meta.info.typ)
        in
        let tv =
          compile_typ env (Infer.concretize env mc.map_val.meta.info.typ)
        in
        let bind_key = var_name mc.bind_key in
        let bind_val = var_name mc.bind_val in
        let b = !bound in
        bound := bind_key :: bind_val :: !bound;
        let sk, mk, lpk = comp mc.map_key in
        let sv, mv, lpv = comp mc.map_val in
        bound := b;
        let si, inp, lpi = comp mc.inp in
        let res = fresh_variable () in
        let k1 = fresh_variable () in
        let v1 = fresh_variable () in
        let sp, pred, lpp =
          match mc.pred with None -> ([], "", []) | Some p -> comp p
        in
        let mapcomp =
          List.concat
            [
              [
                "// map comprehension";
                Format.sprintf "%s := map[%s]%s{}" res tk tv;
                Format.sprintf "for %s, %s := range (%s) {" bind_key bind_val
                  inp;
              ];
              (match mc.pred with
              | None -> []
              | Some _ -> [Format.sprintf "if %s {" pred]);
              [
                Format.sprintf "%s, %s := (%s), (%s)" k1 v1 mk mv;
                Format.sprintf "%s[%s] = %s" res k1 v1;
              ];
              (match mc.pred with None -> [] | Some _ -> ["}"]);
              ["}"];
            ]
        in
        ( List.concat [sk; sv; si; sp; mapcomp],
          res,
          List.concat [lpk; lpv; lpi; lpp] )
      | MapProj (e, i) ->
        begin
          match (Infer.concretize env e.meta.info.typ, i) with
          | TyRecord _, { expr = String i; _ } ->
            let se, e, lpe = comp e in
            (se, Format.sprintf "%s./*record*/%s" e i, lpe)
          | TyMap _, _ ->
            let se, e, lpe = comp e in
            let si, i, lpi = comp i in
            (List.concat [se; si], Format.sprintf "%s/*map*/[%s]" e i, lpe @ lpi)
          | _ -> bug "cannot index into other types"
        end
      | Let _ -> nyi "compile let"
      | App (f, args1) ->
        let stmts, args, lpa = List.map comp args1 |> List.split3 in
        begin
          match f with
          | "!=" ->
            flags.uses_reflect <- true;
            ( List.concat stmts,
              Format.sprintf "%s(%s)" "!reflect.DeepEqual"
                (String.concat ", " args),
              List.concat lpa )
          | "==" ->
            flags.uses_reflect <- true;
            ( List.concat stmts,
              Format.sprintf "%s(%s)" "reflect.DeepEqual"
                (String.concat ", " args),
              List.concat lpa )
          | "union" ->
            (* union of sets represented as maps *)
            let m = fresh_variable () in
            let a1 = List.nth args 0 in
            let a2 = List.nth args 1 in
            let tk, tv =
              match Infer.concretize env (List.hd args1).meta.info.typ with
              | TyMap (k, v) -> (compile_typ env k, compile_typ env v)
              | _ -> bug "invalid map type"
            in
            let union =
              [
                "// set union";
                Format.sprintf "%s := map[%s]%s{}" m tk tv;
                Format.sprintf "for k, _ := range %s {" a1;
                Format.sprintf "%s[k] = true" m;
                "}";
                Format.sprintf "for k, _ := range %s {" a2;
                Format.sprintf "%s[k] = true" m;
                "}";
              ]
            in
            (List.concat stmts @ union, m, List.concat lpa)
          | "min" ->
            let v = fresh_variable () in
            let a1 = List.nth args 0 in
            let mi =
              [
                "// set min";
                Format.sprintf "%s := int(^uint(0)>>1) // max int" v;
                Format.sprintf "for k, _ := range %s {" a1;
                Format.sprintf "if k < %s {" v;
                Format.sprintf "%s = k" v;
                "}";
                "}";
              ]
            in
            (List.concat stmts @ mi, v, List.concat lpa)
          | "last" ->
            let a = List.nth args 0 in
            ( List.concat stmts,
              Format.sprintf "%s[len(%s)-1]" a a,
              List.concat lpa )
          | "slice" ->
            let a = List.nth args 0 in
            let u = List.nth args 1 in
            let l = List.nth args 2 in
            ( List.concat stmts,
              Format.sprintf "%s[%s:%s]" a u l,
              List.concat lpa )
          | "append" when false ->
            (* appending two maps, which can't be implemented generically *)
            let v = fresh_variable () in
            let m = fresh_variable () in
            let a1 = List.nth args 0 in
            let a2 = List.nth args 1 in
            let tk, tv =
              match Infer.concretize env (List.hd args1).meta.info.typ with
              | TyMap (k, v) -> (compile_typ env k, compile_typ env v)
              | _ -> bug "invalid map type"
            in
            let app =
              [
                "// map append";
                Format.sprintf "%s := map[%s]%s{}" m tk tv;
                Format.sprintf "%s := len(%s)" v a1;
                Format.sprintf "for k, v := range %s {" a1;
                Format.sprintf "%s[%s] = v" m v;
                "}";
                Format.sprintf "for k, v := range %s {" a2;
                Format.sprintf "%s[%s+k] = v" m v;
                "}";
              ]
            in
            (List.concat stmts @ app, m, List.concat lpa)
          | "append" ->
            let a = List.nth args 0 in
            let b = List.nth args 1 in
            ( List.concat stmts,
              Format.sprintf "append(%s, %s...)" a b,
              List.concat lpa )
          | _ when List.length args = 2 && not (is_alpha f.[0]) ->
            let f =
              let f1 = match f with "|" -> "||" | "&" -> "&&" | _ -> f in
              Format.sprintf "(%s %s %s)" (List.nth args 0) f1 (List.nth args 1)
            in
            (* operators *)
            (List.concat stmts, f, List.concat lpa)
          | _ ->
            (* simple renamings *)
            let f1 = match f with "size" | "length" -> "len" | _ -> f in
            ( List.concat stmts,
              Format.sprintf "%s(%s)" f1 (String.concat ", " args),
              List.concat lpa )
        end
      | Var (V (_, "self")) -> ([], "m.vars[\"Self\"].(string)", [])
      | Var (V (_, v)) when List.mem ~eq:String.equal v (List.map fst params) ->
        log "var params %s %a" v (List.pp String.pp) (List.map fst params);
        (check_lparam_key v, Format.sprintf "lparams[\"%s\"]" v, [])
      | Var (V (_, v)) when List.mem ~eq:String.equal v parties ->
        log "var parties %s" v;
        (* when compiling to LTL, l.vars is a collection of atomic propositions *)
        (* this is to access party sets *)
        ( [],
          Format.sprintf "m.vars[\"%s\"].(map[string]bool)" (snake_to_camel v),
          [] )
        (* ([], Format.sprintf "g.%s" (snake_to_camel v)) *)
      | Var (V (_, v)) when List.mem ~eq:String.equal v !bound ->
        log "var bound %s" v;
        ([], v, [])
      | Var (V (_, v)) ->
        log "var state %s" v;
        ([], Format.sprintf "g.%s" (snake_to_camel v), [])
      | Record kvs ->
        let record_name = record_name_of kvs in
        let stmts, kvs1, lpa =
          List.map
            (fun (k, v) ->
              let s, v, lp = comp v in
              (s, (k, v), lp))
            kvs
          |> List.split3
        in
        let fields =
          kvs1
          |> List.map (fun (k, v) -> Format.sprintf "%s: %s" k v)
          |> String.concat ", "
        in
        let field_types =
          kvs
          |> List.map (fun (k, v) ->
                 Format.sprintf "%s %s" k
                   (compile_typ env (Infer.concretize env v.meta.info.typ)))
          |> String.concat "\n"
        in
        declare_type record_name field_types;
        ( List.concat stmts,
          Format.sprintf "%s{%s}" (snake_to_camel record_name) fields,
          List.concat lpa )
    in
    comp te

let compile_protocol params env parties tp =
  log "compiling %a, %a" Print.pp_tprotocol_untyped tp (List.pp String.pp)
    (List.map fst params);
  let rec comp (tp : tprotocol) : string list * string list =
    match tp.p with
    | Emp -> (["// skip"], [])
    | Seq ps ->
      let stmts, lparams = List.map comp ps |> List.split in
      (List.concat stmts, List.concat lparams)
    | Call { f; _ } ->
      (* maybe this should be optimized away *)
      (["// call " ^ f], [])
    | Assign ({ expr = Var (V (_, v)); _ }, e) ->
      let stmts, e, lparams = compile_expr params env parties e in
      (stmts @ [Format.sprintf "g.%s = %s" (snake_to_camel v) e], lparams)
    | Assign (e, e1) ->
      let se, e, lpe = compile_expr params env parties e in
      let se1, e1, lpe1 = compile_expr params env parties e1 in
      (se @ se1 @ [Format.sprintf "g.%s = %s" e e1], lpe @ lpe1)
    | SendOnly { to_; msg = Message { typ; args } } ->
      let to_ = var_name (Infer.Cast.must_be_var_t to_) in
      let stmts, args, lp =
        List.map
          (fun (fn, fv) ->
            let fn = var_name (Infer.Cast.must_be_var_t fn) in
            let sfv, fv, lp = compile_expr params env parties fv in
            (sfv, (fn, fv), lp))
          args
        |> List.split3
      in
      let check_lparam, param_to =
        match to_ with
        | "self" -> ([], "m.vars[\"Self\"]")
        | _ -> (check_lparam_key to_, Format.sprintf "lparams[\"%s\"]" to_)
      in
      let fields =
        [("type", Format.sprintf "\"%s\"" typ); ("to", param_to)] @ args
      in
      let fields =
        fields
        |> List.map (fun (k, v) -> Format.sprintf "\"%s\": %s" k v)
        |> String.concat ","
      in
      ( List.concat stmts
        (* check_lparam must come first *)
        @ check_lparam
        @ [Format.sprintf "g.History1 = map[string]interface{}{%s}" fields],
        List.concat lp )
    | ReceiveOnly { from; msg = MessageD { typ; args } } ->
      let from = var_name (Infer.Cast.must_be_var_t from) in
      let check_lparam, param_from =
        match from with
        | "self" -> ([], "m.vars[\"Self\"]")
        | _ -> (check_lparam_key from, Format.sprintf "lparams[\"%s\"]" from)
      in
      let fields =
        [("type", Format.sprintf "\"%s\"" typ); ("from", param_from)]
        @ List.map
            (fun fn ->
              let fn = var_name (Infer.Cast.must_be_var_t fn) in
              (fn, "true"))
            args
      in
      let fields =
        fields
        |> List.map (fun (k, v) -> Format.sprintf "\"%s\": %s" k v)
        |> String.concat ","
      in
      (* check_lparam must come first *)
      ( check_lparam
        @ [Format.sprintf "g.History1 = map[string]interface{}{%s}" fields],
        [] )
    (* not expected *)
    | Exists (_, _, _) -> nyi "Exists"
    | Imply _ -> nyi "Imply should have been translated away"
    | BlockingImply (_, _) ->
      nyi "BlockingImply should have been translated away"
    | Forall (_, _, _) -> nyi "Forall should have been translated away"
    | Send _ -> nyi "Send should have been translated away"
    | Comment _ -> nyi "Comment"
    | Par _ -> bug "Par should have been translated away"
    | Disj _ -> bug "Disj should have been translated away"
  in
  let ss, lp = comp tp in
  (String.concat "\n" ss, lp)

let check_monitorability env ltl node_colors =
  if
    SMap.bindings node_colors
    |> List.for_all (fun (_, c) -> String.equal "yellow" c)
  then bad_input "%a is not monitorable" (Print.pp_texpr ~env) ltl

let generate_ltl_monitor ltl_i env parties pname ltl =
  let ltl1, bindings = extract_subexprs env ltl in
  let fml = ltl1 |> fml_to_ltl3tools in
  let output = fml |> invoke_ltl2mon in
  if debug then
    (* TODO re-print the graphviz file with updated names? *)
    write_to_file ~filename:(Format.sprintf "ltl-%s-%d.dot" pname ltl_i) output;
  let node_colors, edges, graph = output |> parse_graphviz_output in
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
           else Format.sprintf "%s := l.%s(g)" v v)
    |> String.concat "\n"
  in
  let prop_fns =
    bindings |> SMap.bindings
    |> List.map (fun (v, te) ->
           let stmt, te, lp = compile_expr [] env parties te in
           Format.sprintf
             "func (l *LTLMonitor%d) %s(g Global) bool {\n%sreturn %s\n}" ltl_i
             v
             (stmt |> String.concat "\n")
             te)
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
            flags.uses_errors <- true;
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

let pc = "PC"

let tid_to_go bound (t : tid) : go_expr =
  match t.params with
  | [] -> ([], Format.sprintf "\"%s\"" t.name)
  | _ ->
    let checks, params =
      t.params
      |> List.map (fun (v, s) ->
             if List.mem_assoc ~eq:String.equal v bound then
               ([], Format.sprintf "%s" v)
             else
               (* TODO invalid go code *)
               let ps = Format.asprintf "%a" Print.pp_party_set s in
               let check = check_cparam_key v in
               (check, Format.asprintf "cparams[\"%s\"] /* : %s */" v ps))
      |> List.split
    in
    ( List.concat checks,
      Format.sprintf "\"%s_\" + (%s)" t.name (String.concat "+" params) )

let cfml_to_precondition (f : cfml) : go_expr =
  let open Actions in
  let rec aux bound f =
    match f with
    | ThreadStart tid ->
      let checks, tid = tid_to_go bound tid in
      (checks, Format.sprintf "m.%s[%s] == %d" pc tid default_pc_value)
    | AnyOf fs ->
      let checks, tid = List.map (aux bound) fs |> List.split in
      (List.concat checks, tid |> String.concat " || ")
    | AllOf fs ->
      let checks, tid = List.map (aux bound) fs |> List.split in
      (List.concat checks, tid |> String.concat " && ")
    | CForall (v, s, z) ->
      let ps = Format.asprintf "%a" Print.pp_party_set s in
      let checks, body = aux ((v, s) :: bound) z in
      ( checks,
        Format.sprintf
          "allSet(m.vars[\"%s\"].(map[string]bool), func(%s string) bool { \
           return %s })"
          ps v body )
    | Eq (tid, i) ->
      let checks, tid = tid_to_go bound tid in
      (checks, Format.sprintf "m.%s[%s] == %d" pc tid i)
  in
  aux [] f

let cfml_to_postcondition (f : cfml) : go_expr =
  let rec aux bound f =
    match f with
    | AllOf fs ->
      let checks, post = List.map (aux bound) fs |> List.split in
      (List.concat checks, post |> String.concat ";\n")
    | Eq (tid, i) ->
      let checks, tid = tid_to_go bound tid in
      (checks, Format.sprintf "m.%s[%s] = %d" pc tid i)
      (* postconditions are more restrictive than preconditions *)
    | CForall _ -> nyi "cforall to postcondition"
    | ThreadStart _ ->
      bug
        "possible to have ThreadStart in a postcondition (as then there would \
         be an action without any control flow)"
    | AnyOf _ ->
      bug "not possible to have AnyOf in a postcondition (nondeterminism)"
  in
  aux [] f

let should_generate_ltl_monitor = false

let translate_party_ltl env ltl_i pname ltl action_nodes parties =
  (* TODO use pname to qualify stuff *)
  let ltl_monitors =
    if should_generate_ltl_monitor then
      List.map (generate_ltl_monitor ltl_i env parties pname) ltl
    else []
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
  let assigned =
    IMap.bindings action_nodes
    |> List.concat_map
         Actions.(fun (_, ac) -> abstract_state_variables ac.protocol)
    |> List.sort_uniq ~cmp:(fun (a, _) (b, _) -> String.compare a b)
  in
  log "assigned variables: %a" (List.pp String.pp) (List.map fst assigned);

  (* start filling in the template *)
  let preconditions =
    let open Actions in
    IMap.bindings action_nodes
    |> List.map (fun (id, act) ->
           let name = Actions.node_name pname (id, act) in
           let lpre =
             match act.lpre with
             | [] -> "// no logical preconditions"
             | _ ->
               act.lpre
               |> List.map (fun p ->
                      let stmts, p, lp = compile_expr [] env parties p in
                      Format.sprintf
                        {|%sif g != nil && !(%s) {
              return fmt.Errorf("logical precondition of %%s, %%#v violated", "%s", lparams)
            }|}
                        (match stmts with
                        | [] -> ""
                        | _ -> (stmts |> String.concat "\n") ^ "\n")
                        p name)
               |> String.concat "\n"
           in
           let stmts, pre = cfml_to_precondition act.cpre in
           Format.sprintf
             {|case %s:
             %s
             %s
             if ! (%s) {
               return fmt.Errorf("control precondition of %s %%v violated", cparams)
             }
             return nil|}
             name lpre
             (stmts |> String.concat "\n")
             pre name)
    |> String.concat "\n"
  in
  let postconditions =
    let open Actions in
    IMap.bindings action_nodes
    |> List.map (fun (id, act) ->
           (* let tid = act.protocol.pmeta.tid in
              Format.sprintf
                {|case %s:
              %s
              m.%s[%s] = %d|}
                (Actions.node_name pname (id, act))
                (params_check act.params) pc (tid_to_string [] tid) id *)
           (* let tid = act.protocol.pmeta.tid in *)
           let checks, post = cfml_to_postcondition act.cpost in
           Format.sprintf
             {|case %s:
             %s
           %s|}
             (Actions.node_name pname (id, act))
             (String.concat "\n" checks)
             post)
    |> String.concat "\n"
  in
  let protocol_effects =
    let open Actions in
    IMap.bindings action_nodes
    |> List.map (fun (id, act) ->
           (* let tid = act.protocol.pmeta.tid in *)
           let ss, lp = compile_protocol act.params env parties act.protocol in
           Format.sprintf
             {|case %s:
           %s
           return nil|}
             (Actions.node_name pname (id, act))
             ss)
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
    let vars =
      assigned
      |> List.map (fun (v, info) ->
             Format.sprintf "%s %s" (snake_to_camel v)
               (compile_typ env info.typ))
    in
    let vars = "History1 map[string]interface{}" :: vars in
    vars |> String.concat "\n"
  in
  let extra_imports =
    String.concat "\n"
    @@ List.concat
         [
           (* (if flags.uses_reflect then ["\"reflect\""] else []); *)
           (if flags.uses_errors then ["\"errors\""] else []);
         ]
  in
  let declared_types =
    flags.declared_types
    |> List.map (fun (name, def) ->
           Format.sprintf "type %s struct {\n%s\n}" (snake_to_camel name) def)
    |> String.concat "\n"
  in
  template_monitor
    ~pname:(String.lowercase_ascii pname)
    ~extra_imports ~global_contents ~action_defs ~preconditions ~postconditions
    ~ltl_monitor_defs ~ltl_monitor_fields ~ltl_monitor_assignments
    ~ltl_monitor_init ~ltl_monitor_step ~protocol_effects ~declared_types ()

let translate_party_ltl env i pname ltl action_nodes parties =
  (* reset state *)
  restore_flags ();
  log "generating monitor for party %s" pname;
  action_nodes
  |> IMap.iter
       Actions.(
         fun i a -> log "%d %a" i (List.pp String.pp) (List.map fst a.params));
  if not (IMap.is_empty action_nodes) then
    let code =
      translate_party_ltl env i pname ltl action_nodes parties |> invoke_gofmt
    in
    write_to_file ~filename:(Format.sprintf "monitor%s.go" pname) code
