open Containers

type party = Party of string [@@deriving ord, eq]

let pp_party fmt (Party p) = Format.fprintf fmt "%s" p

type var = V of party option * string [@@deriving ord, eq]

let pp_var fmt (V (p, var)) =
  match p with
  | Some p -> Format.fprintf fmt "%a.%s" pp_party p var
  | None -> Format.fprintf fmt "%s" var

let var s = V (None, s)

(* let ( >. ) (V (_, c)) s = V (Some (Party c), s)  *)

let ( >. ) (V (_, c)) (V (_, s)) = V (Some (Party c), s)

let var_name (V (_, v)) = v

let var_names vars = List.map var_name vars

let pp_const s fmt () = Format.fprintf fmt "%s" s

let pp_literal fmt s = Format.fprintf fmt "%s" s

module VMap = struct
  module M = Map.Make (struct
    type t = var

    let compare = compare_var
  end)

  include M

  let pp e fmt map =
    Format.fprintf fmt "%a"
      (M.pp ~pp_sep:(pp_const ";") ~pp_start:(pp_const "{")
         ~pp_stop:(pp_const "}") pp_var e)
      map
end

module SMap = struct
  module M = Map.Make (String)
  include M

  let pp e fmt map =
    Format.fprintf fmt "%a"
      (M.pp ~pp_sep:(pp_const ";") ~pp_start:(pp_const "{")
         ~pp_stop:(pp_const "}") String.pp e)
      map
end

module IMap = struct
  module M = Map.Make (Int)
  include M

  let pp e fmt map =
    Format.fprintf fmt "%a"
      (M.pp ~pp_sep:(pp_const ";") ~pp_start:(pp_const "{")
         ~pp_stop:(pp_const "}") Int.pp e)
      map
end

type expr =
  | Int of int
  | Bool of bool
  | Set of expr list
  | List of expr list
  | Map of (string * expr) list
  | App of string * expr list
  | Var of var
  | Tuple of expr * expr
[@@deriving eq, show { with_path = false }]

let plus a b = App ("+", [a; b])

let eq a b = App ("==", [a; b])

let geq a b = App (">=", [a; b])

let gt a b = App (">", [a; b])

let and_ a b = App ("&", [a; b])

let or_ a b = App ("|", [a; b])

let rec pp_expr fmt e =
  let open Format in
  match e with
  | Int i -> fprintf fmt "%d" i
  | Bool b -> fprintf fmt "%b" b
  | App (name, es) ->
    if List.length es = 2 then
      fprintf fmt "@[%a@ %s@ %a@]" pp_expr (List.nth es 0) name pp_expr
        (List.nth es 1)
    else
      fprintf fmt "%s(%a)" name (List.pp pp_expr) es
  | Var v -> pp_var fmt v
  | Set s -> fprintf fmt "{%a}" (List.pp pp_expr) s
  | List s -> fprintf fmt "[%a]" (List.pp pp_expr) s
  | Map s ->
    fprintf fmt "{%a}"
      (List.pp
         (Pair.pp ~pp_sep:(pp_const ": ") ~pp_start:(pp_const "")
            ~pp_stop:(pp_const "") pp_literal pp_expr))
      s
  | Tuple (a, b) -> fprintf fmt "<%a, %a>" pp_expr a pp_expr b

type msg =
  | Message of {
      typ : string;
      args : (var * expr) list;
    }
[@@deriving eq]

type msg_destruct =
  | MessageD of {
      typ : string;
      args : var list;
    }
[@@deriving eq]

type msg_construct =
  | MessageC of {
      typ : string;
      args : expr list;
    }
[@@deriving eq]

let msg name = Message { typ = name; args = [] }

let msg_destruct (Message { typ; args }) =
  MessageD { typ; args = List.map fst args }

let msg_construct (Message { typ; args }) =
  MessageC { typ; args = List.map snd args }

let pp_msg fmt (Message { typ; args }) =
  Format.fprintf fmt "%s%s" typ
    (match args with
    | [] -> ""
    | _ ->
      args
      |> List.map (fun (k, v) -> Format.sprintf "%a=%a" pp_var k pp_expr v)
      |> String.concat ", "
      |> fun a -> "(" ^ a ^ ")")

let pp_msg_construct fmt (MessageC { typ; args }) =
  Format.fprintf fmt "%s%s" typ
    (match args with
    | [] -> ""
    | _ ->
      args
      |> List.map (fun v -> Format.sprintf "%a" pp_expr v)
      |> String.concat ", "
      |> fun a -> "(" ^ a ^ ")")

let pp_msg_destruct fmt (MessageD { typ; args }) =
  Format.fprintf fmt "%s%s" typ
    (match args with
    | [] -> ""
    | _ ->
      args
      |> List.map (fun k -> Format.sprintf "%a" pp_var k)
      |> String.concat ", "
      |> fun a -> "(" ^ a ^ ")")

type protocol =
  | Emp
  | Seq of protocol list
  | Par of protocol list
  | Disj of protocol * protocol
  | Send of {
      from : var;
      to_ : var;
      msg : msg;
    }
  | Assign of var * expr
  | Imply of expr * protocol
  | BlockingImply of expr * protocol
  (* TODO use bindlib? *)
  | Forall of var * var * protocol
  | Exists of var * var * protocol
  (* extras *)
  | SendOnly of {
      from : var;
      to_ : var;
      msg : msg_construct;
    }
  | ReceiveOnly of {
      from : var;
      to_ : var;
      msg : msg_destruct;
    }
  (* cst *)
  | Comment of var option * string * protocol
(* cst would have parens too *)
[@@deriving eq, show { with_path = false }]
