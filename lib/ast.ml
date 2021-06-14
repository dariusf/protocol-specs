open Containers
open Common

type party = Party of string [@@deriving ord, eq]

let pp_party fmt (Party p) = Format.fprintf fmt "%s" p

type var = V of party option * string [@@deriving ord, eq]

let var_name (V (_, v)) = v

let var_names vars = List.map var_name vars

let pp_var fmt (V (p, var)) =
  match p with
  | Some p -> Format.fprintf fmt "%a.%s" pp_party p var
  | None -> Format.fprintf fmt "%s" var

let var s = V (None, s)

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

type typ =
  | TyParty of UF.t
  | TySet of typ
  | TyList of typ
  | TyVar of UF.t
  | TyInt
  | TyBool
  | TyString
  | TyFn of typ list * typ
[@@deriving show { with_path = false }, eq]

type meta = { loc : loc }

type ownership =
  | Global
  | Party of UF.t
[@@deriving show { with_path = false }, eq]

type var_info = {
  typ : typ;
  own : ownership;
}
[@@deriving show { with_path = false }, eq]

type tmeta = {
  loc : loc;
  info : var_info;
}
[@@deriving show { with_path = false }, eq]

type 'a _expr = {
  meta : 'a;
  expr : 'a _expr';
}

and 'a _expr' =
  | Int of int
  | Bool of bool
  | String of string
  | Timeout
  | Else
  | Set of 'a _expr list
  | List of 'a _expr list
  | Map of (string * 'a _expr) list
  | App of string * 'a _expr list
  | Var of var
  | Tuple of 'a _expr * 'a _expr
[@@deriving show { with_path = false }, eq]

type expr = loc _expr [@@deriving show { with_path = false }, eq]

type texpr = tmeta _expr [@@deriving show { with_path = false }, eq]

let with_pos start stop expr =
  Lexing.
    {
      meta =
        {
          start =
            { line = start.pos_lnum; col = start.pos_cnum - start.pos_bol };
          stop = { line = stop.pos_lnum; col = stop.pos_cnum - stop.pos_bol };
        };
      expr;
    }

let plus a b = App ("+", [a; b])

let eq a b = App ("==", [a; b])

let geq a b = App (">=", [a; b])

let gt a b = App (">", [a; b])

let and_ a b = App ("&", [a; b])

let or_ a b = App ("|", [a; b])

type ('e, 'v) msg =
  | Message of {
      typ : string;
      args : ('v * 'e) list;
    }
[@@deriving show { with_path = false }, eq]

type 'v msg_destruct =
  | MessageD of {
      typ : string;
      args : 'v list;
    }
[@@deriving show { with_path = false }, eq]

let msg name = Message { typ = name; args = [] }

let msg_destruct (Message { typ; args }) =
  MessageD { typ; args = List.map fst args }

type ('a, 'e, 'v) _protocol = {
  pmeta : 'a;
  p : ('a, 'e, 'v) _protocol';
}

and ('a, 'e, 'v) _protocol' =
  | Emp
  | Seq of ('a, 'e, 'v) _protocol list
  | Par of ('a, 'e, 'v) _protocol list
  | Disj of ('a, 'e, 'v) _protocol * ('a, 'e, 'v) _protocol
  | Call of string * 'e list
  | Send of {
      from : 'v;
      to_ : 'v;
      msg : ('e, 'v) msg;
    }
  | Assign of 'v * 'e
  | Imply of 'e * ('a, 'e, 'v) _protocol
  | BlockingImply of 'e * ('a, 'e, 'v) _protocol
  (* TODO use bindlib? *)
  | Forall of 'v * 'e * ('a, 'e, 'v) _protocol
  | Exists of 'v * 'e * ('a, 'e, 'v) _protocol
  (* extras *)
  | SendOnly of {
      to_ : 'v;
      msg : ('e, 'v) msg;
    }
  | ReceiveOnly of {
      from : 'v;
      msg : 'v msg_destruct;
    }
  (* cst *)
  | Comment of var option * string * ('a, 'e, 'v) _protocol
(* cst would have parens too *)
[@@deriving show { with_path = false }, eq]

let must_be_var e =
  match e.expr with
  | Var v -> v
  | _ -> failwith (Format.sprintf "%a must be a var" pp_expr e)

let must_be_var_t e =
  match e.expr with
  | Var v -> v
  | _ -> failwith (Format.sprintf "%a must be a var" pp_texpr e)

type protocol = (loc, expr, expr) _protocol
[@@deriving show { with_path = false }, eq]

type tid = {
  name : string;
  params : (string * string) list;
}
[@@deriving show { with_path = false }, eq]

type pmeta = {
  tid : tid;
  loc : loc;
}
[@@deriving show { with_path = false }, eq]

let pmeta ?(tid = { name = "main"; params = [] }) ~loc () = { loc; tid }

type tprotocol = (pmeta, texpr, texpr) _protocol
[@@deriving show { with_path = false }, eq]

let p_with_pos start stop p =
  Lexing.
    {
      pmeta =
        {
          start =
            { line = start.pos_lnum; col = start.pos_cnum - start.pos_bol };
          stop = { line = stop.pos_lnum; col = stop.pos_cnum - stop.pos_bol };
        };
      p;
    }

type party_info = { (* representative set, will be nonempty *)
                    repr : var }
[@@deriving show { with_path = false }, eq]

let empty_party_info repr = { repr }

type scheme = Forall of UF.t list * typ
[@@deriving show { with_path = false }]

type subprotocol = {
  fname : string;
  fparams : string list;
  tp : tprotocol;
  initiator : string;
}
[@@deriving show { with_path = false }]

type env = {
  (* known parties and types *)
  parties : party_info IMap.t;
  types : typ IMap.t;
  (* tracks the types of variables, will have pointers into above fields *)
  bindings : var_info SMap.t;
  local_bindings : var_info SMap.t;
  polymorphic : scheme SMap.t;
  subprotocols : subprotocol SMap.t;
}
[@@deriving show { with_path = false }]

let empty_env =
  {
    parties = IMap.empty;
    types = IMap.empty;
    bindings = SMap.empty;
    local_bindings = SMap.empty;
    polymorphic = SMap.empty;
    subprotocols = SMap.empty;
  }

let party_list parties = parties |> IMap.values |> List.of_iter

type spec_decl =
  | Invariant of expr
  | Ltl of expr
  | Function of string * string list * protocol
[@@deriving show { with_path = false }]

type spec = {
  decls : spec_decl list;
  protocol : protocol;
}
[@@deriving show { with_path = false }]
