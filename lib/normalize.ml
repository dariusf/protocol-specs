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
    | Seq [] -> Emp
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
        | (a, _) when not (useful a) ->
          (* stuff like this changes whether the metadata of an expression or a subexpression is used *)
          (normalize_once b).p
        | (_, b) when not (useful b) -> (normalize_once a).p
        | _ -> Disj (normalize_once a, normalize_once b)
      end
    | Emp | Send _ | Assign (_, _) -> p.p
    | Imply (c, p) -> Imply (c, normalize_once p)
    | BlockingImply (c, p) -> BlockingImply (c, normalize_once p)
    | Forall (v, s, p) -> Forall (v, s, normalize_once p)
    | Exists (v, s, p) -> Exists (v, s, normalize_once p)
    | SendOnly _ | ReceiveOnly _ -> p.p
    | Comment (pa, s, p) -> Comment (pa, s, normalize_once p)
  in
  { p with p = p1 }

let rec normalize p =
  let p1 = normalize_once p in
  if equal_protocol p p1 then
    p1
  else
    normalize p1

let rec normalize_t p =
  let p1 = normalize_once p in
  if equal_tprotocol p p1 then
    p1
  else
    normalize_t p1
