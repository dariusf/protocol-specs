open Ast
open Containers
open Common
open Infer
open Normalize

let replace_self party v =
  if List.mem ~eq:equal_var v party.vars then
    var "self"
  else
    v

(* parties is a list of (party name, vars belonging to it) *)
let project env pr =
  let rec aux pr =
    match pr with
    | Emp -> env.parties |> List.map (fun _ -> Emp)
    | Assign (v, e) ->
      env.parties
      |> List.map (fun party ->
             if is_owned_by party v then
               (* leave unqualified for now, since unqualified vars after this become emp anyway *)
               Assign (v, e)
             else
               Emp)
    | Seq ps -> ps |> List.map aux |> transpose |> List.map (fun p -> Seq p)
    | Par ps -> ps |> List.map aux |> transpose |> List.map (fun p -> Par p)
    | Disj (a, b) ->
      [a; b] |> List.map aux |> transpose
      |> List.map (function [a; b] -> Disj (a, b) | _ -> failwith "invalid")
    | Send { from; to_; msg } ->
      env.parties
      |> List.map (fun party ->
             if List.mem ~eq:equal_var from party.vars then
               SendOnly
                 {
                   from = replace_self party from;
                   to_ = replace_self party to_;
                   msg = msg_construct msg;
                 }
             else if List.mem ~eq:equal_var to_ party.vars then
               ReceiveOnly
                 {
                   from = replace_self party from;
                   to_ = replace_self party to_;
                   msg = msg_destruct msg;
                 }
             else
               Emp)
    | Imply (c, body) ->
      List.map2
        (fun party body1 ->
          if List.for_all (is_owned_by party) (vars_in c) then
            Imply (c, body1)
          else (* note that this is the body of the conditional, not emp *)
            body1)
        env.parties (aux body)
    | BlockingImply (c, body) ->
      List.map2
        (fun party body1 ->
          if List.for_all (is_owned_by party) (vars_in c) then
            BlockingImply (c, body1)
          else
            body1)
        env.parties (aux body)
    | Forall (v, s, p) ->
      (* env.parties |> List.map (fun _ -> p) *)
      List.map2
        (fun party p1 ->
          (* Format.printf "v %a party %a@." pp_var v (List.pp pp_var) party.vars; *)
          if List.mem ~eq:equal_var v party.vars then
            p1
          else
            Forall (v, s, p1))
        env.parties (aux p)
    | Exists (v, s, p) ->
      List.map2
        (fun party p1 ->
          if List.mem ~eq:equal_var v party.vars then
            p1
          else
            Exists (v, s, p1))
        env.parties (aux p)
    | SendOnly _ -> fail "send only should not be used in front end language"
    | ReceiveOnly _ ->
      fail "receive only should not be used in front end language"
    | Comment (party, s, p) ->
      List.map2
        (fun party1 p1 ->
          match party with
          | None -> p1
          | Some party2 ->
            if equal_var party2 party1.repr then Comment (party, s, p1) else p1)
        env.parties (aux p)
  in
  aux pr |> List.map normalize
