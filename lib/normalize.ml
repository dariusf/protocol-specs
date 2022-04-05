open Containers
open Ast

let rec normalize_once p =
  let rec useful p =
    match p.p with
    | Emp | Seq [] -> false
    | Forall (_, _, p) | Exists (_, _, p) -> useful p
    | _ -> true
  in
  let p1 =
    match p.p with
    | Seq [] | Par [] -> Emp
    | Seq [s] | Par [s] -> s.p
    | Seq s ->
      let s = s |> List.map normalize_once |> List.filter useful in
      Seq
        (s
        |> List.concat_map (fun p -> match p.p with Seq ps -> ps | _ -> [p]))
    | Par s ->
      let s = s |> List.map normalize_once |> List.filter useful in
      Par
        (s
        |> List.concat_map (fun p -> match p.p with Par ps -> ps | _ -> [p]))
    | Disj (a, b) ->
      begin
        match (a, b) with
        | a, _ when not (useful a) ->
          (* stuff like this changes whether the metadata of an expression or a subexpression is used *)
          (normalize_once b).p
        | _, b when not (useful b) -> (normalize_once a).p
        | _ -> Disj (normalize_once a, normalize_once b)
      end
    | Emp | Send _ | Assign _ | Call _ -> p.p
    | Imply (_, { p = Emp; _ }) -> Emp
    | Imply (c, p) -> Imply (c, normalize_once p)
    | BlockingImply (_, { p = Emp; _ }) -> Emp
    | BlockingImply (c, p) -> BlockingImply (c, normalize_once p)
    | Forall (_, _, { p = Emp; _ }) -> Emp
    | Forall (v, s, p) -> Forall (v, s, normalize_once p)
    | Exists (_, _, { p = Emp; _ }) -> Emp
    | Exists (v, s, p) -> Exists (v, s, normalize_once p)
    | SendOnly _ | ReceiveOnly _ -> p.p
    | Comment (pa, s, p) -> Comment (pa, s, normalize_once p)
  in
  { p with p = p1 }

let rec normalize p =
  let p1 = normalize_once p in
  if equal_protocol p p1 then p1 else normalize p1

let rec normalize_t p =
  let p1 = normalize_once p in
  if equal_tprotocol p p1 then p1 else normalize_t p1

let interpret_seq_of_assignments_as_specparty bs =
  let bindings =
    List.filter_map
      (fun x ->
        match x.p with
        | Assign ({ expr = Var (V (q, v)); _ }, e) -> Some (q, v, e)
        | _ ->
          (* can also ignore and drop *)
          failwith
            ("must be a seq of assignments "
            ^ Format.asprintf "%a" pp_protocol x))
      bs
  in
  let vars =
    bindings
    |> List.filter_map (fun (q, v, e) ->
           match q with Some _ -> Some (v, e) | None -> None)
  in
  let size =
    bindings
    |> List.filter_map (fun (q, v, e) ->
           match (q, v, e.expr) with None, "size", Int i -> Some i | _ -> None)
    |> List.head_opt |> Option.get_or ~default:0
  in
  (vars, size)

let to_specparty var set b =
  let initial, size =
    match b with
    | None -> ([], 0)
    | Some b ->
      (* normalize so nested seqs are flattened into a single top-level seq *)
      (match (normalize b).p with
      | Seq xs -> interpret_seq_of_assignments_as_specparty xs
      | Assign ({ expr = Var (V (_, _)); _ }, _) ->
        interpret_seq_of_assignments_as_specparty [b]
      | _ -> failwith "must be a seq of assignments")
  in
  SpecParty { var; set; initial; size }