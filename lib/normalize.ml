open Ast

let rec normalize_once p =
  (* let%trace rec normalize_once : protocol -> protocol = fun p -> *)
  let rec useful = function
    | Emp | Seq [] -> false
    | Forall (_, _, p) | Exists (_, _, p) -> useful p
    | _ -> true
  in
  (* let aux p = *)
  match p with
  (* what's this for? *)
  (* | Seq [s] -> normalize_once s *)
  | Seq s ->
    let s = s |> List.map normalize_once |> List.filter useful in
    Seq (s |> List.concat_map (fun p -> match p with Seq ps -> ps | _ -> [p]))
  | Par s ->
    let s = s |> List.map normalize_once |> List.filter useful in
    Par (s |> List.concat_map (fun p -> match p with Par ps -> ps | _ -> [p]))
  | Disj (a, b) ->
    begin
      match (a, b) with
      | (a, _) when not (useful a) -> normalize_once b
      | (_, b) when not (useful b) -> normalize_once a
      | _ -> Disj (normalize_once a, normalize_once b)
    end
  | Emp -> p
  | Send _ -> p
  | Assign (_, _) -> p
  | Imply (c, p) -> Imply (c, normalize_once p)
  | BlockingImply (c, p) -> BlockingImply (c, normalize_once p)
  | Forall (v, s, p) -> Forall (v, s, normalize_once p)
  | Exists (v, s, p) -> Exists (v, s, normalize_once p)
  | SendOnly _ -> p
  | ReceiveOnly _ -> p
  | Comment (pa, s, p) -> Comment (pa, s, normalize_once p)

(* in let r = aux p in *)
(* if useful r then Some r else None *)

let rec normalize p =
  let p1 = normalize_once p in
  (* print_endline "normalize"; *)
  if equal_protocol p p1 then
    p1
  else
    normalize p1
