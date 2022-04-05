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

module Typ = struct
  type typ =
    | TyParty of UF.t
    (* | ty_set of typ *)
    (* | ty_list of typ *)
    | TyMap of typ * typ
    | TyRecord of (string * typ) list
    | TyVar of UF.t
    | TyInt
    | TyBool
    | TyString
    | TyFn of typ list * typ
  [@@deriving
    show { with_path = false },
      eq,
      visitors { variety = "map"; name = "map" },
      visitors { variety = "reduce"; name = "reduce" }]

  let ty_set t = TyMap (t, TyBool)
  let ty_list t = TyMap (TyInt, t)

  class ['self] map_typ =
    object (_ : 'self)
      inherit [_] map
      method visit_t _env t = t
    end

  class virtual ['self] reduce_typ =
    object (self : 'self)
      inherit [_] reduce
      method visit_t _env _ = self#zero
    end

  class ['self] reduce_typ_list =
    object (self : 'self)
      inherit [_] reduce
      method zero = []
      method plus a b = a @ b
      method visit_t _env _ = self#zero
    end
end [@warning "-17"]

include Typ

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

module Expr = struct
  type 'm _expr = {
    meta : 'm;
    expr : 'm _expr';
  }

  and 'm _expr' =
    | Int of int
    | Bool of bool
    | String of string
    | Let of var * 'm _expr * 'm _expr
    | Set of 'm _expr list
    | List of 'm _expr list
    | Map of (string * 'm _expr) list
    | Record of (string * 'm _expr) list
    | MapComp of {
        map_key : 'm _expr;
        map_val : 'm _expr;
        bind_key : var;
        bind_val : var;
        inp : 'm _expr;
        pred : 'm _expr option;
      }
    | MapProj of 'm _expr * 'm _expr
    | App of string * 'm _expr list
    | Var of var
    | Ite of 'm _expr * 'm _expr * 'm _expr
  [@@deriving
    show { with_path = false },
      eq,
      visitors { variety = "map"; name = "map" },
      visitors { variety = "reduce"; name = "reduce" }]

  class ['self] map_expr =
    object (_ : 'self)
      inherit [_] map
      method visit_'m _env m = m
      method visit_var _env v = v
    end

  class virtual ['self] reduce_expr =
    object (self : 'self)
      inherit [_] reduce
      method visit_'m _env _ = self#zero
      method visit_var _env _ = self#zero
    end

  class ['self] reduce_expr_list =
    object (_ : 'self)
      inherit [_] reduce_expr
      method zero = []
      method plus a b = a @ b
    end
end [@warning "-17"]

include Expr

type expr = loc _expr [@@deriving show { with_path = false }, eq]

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
[@@deriving
  show { with_path = false }, eq, visitors { variety = "map"; name = "map_msg" }]

type 'v msg_destruct =
  | MessageD of {
      typ : string;
      args : 'v list;
    }
[@@deriving
  show { with_path = false },
    eq,
    visitors { variety = "map"; name = "map_msg_destruct" }]

let msg name = Message { typ = name; args = [] }

let msg_destruct (Message { typ; args }) =
  MessageD { typ; args = List.map fst args }

module Protocol = struct
  type ('a, 'e, 'v) _protocol = {
    pmeta : 'a;
    p : ('a, 'e, 'v) _protocol';
  }

  and ('a, 'e, 'v) _protocol' =
    | Emp
    | Seq of ('a, 'e, 'v) _protocol list
    | Par of ('a, 'e, 'v) _protocol list
    | Disj of ('a, 'e, 'v) _protocol * ('a, 'e, 'v) _protocol
    | Call of {
        f : string;
        args : 'e list;
      }
    | Send of {
        from : 'v;
        to_ : 'v;
        msg : ('e, 'v) msg;
      }
    | Assign of 'e * 'e
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
  [@@deriving
    show { with_path = false },
      eq,
      visitors { variety = "map"; name = "map" },
      visitors { variety = "reduce"; name = "reduce" }]

  class ['self] map_protocol =
    object (self : 'self)
      inherit [_] map_expr

      (* primitive methods are overriden. doesn't seem to matter which one we use *)
      inherit! [_] map

      (* these methods are called and must be provided *)
      method visit_'a _env m = m
      method visit_'e env m = self#visit__expr env m
      method visit_'v env m = self#visit__expr env m

      method visit_msg ve vv env m =
        let vp =
          object
            inherit [_] map_msg
            method visit_'e env m = ve env m
            method visit_'v env m = vv env m
          end
        in
        vp#visit_msg env m

      method visit_msg_destruct vv env m =
        let vp =
          object
            inherit [_] map_msg_destruct
            method visit_'v env m = vv env m
          end
        in
        vp#visit_msg_destruct env m
    end

  class virtual ['self] reduce_protocol =
    object (self : 'self)
      inherit [_] reduce
      inherit! [_] reduce_expr
      method visit_'a _env _ = self#zero
      method visit_'e env e = self#visit__expr env e
      method visit_'v env v = self#visit__expr env v

      (* this won't recurse inside messages. currently not needed *)
      method visit_msg _ve _vv _env _m = self#zero
      method visit_msg_destruct _vv _env _m = self#zero
    end

  class ['self] reduce_protocol_list =
    object (_ : 'self)
      inherit [_] reduce_protocol
      method zero = []
      method plus a b = a @ b
    end
end [@warning "-17"]

include Protocol

type protocol = (loc, expr, expr) _protocol
[@@deriving show { with_path = false }, eq]

type tid = {
  name : string;
  params : (string * string) list;
}
[@@deriving show { with_path = false }, eq]

type party_info = { (* representative set, will be nonempty *)
                    repr : var }
[@@deriving show { with_path = false }, eq]

let empty_party_info repr = { repr }

type scheme = Forall of UF.t list * typ
[@@deriving show { with_path = false }, eq]

type tmeta = {
  loc : loc;
  info : var_info;
  env : env;
}

and texpr = tmeta _expr

and pmeta = {
  tid : tid;
  ploc : loc;
  penv : env;
}

and tprotocol = (pmeta, texpr, texpr) _protocol

and subprotocol = {
  fname : string;
  fparams : string list;
  tp : tprotocol;
}

and env = {
  (* known parties and types *)
  parties : party_info IMap.t;
  types : typ IMap.t;
  (* tracks the types of variables, will have pointers into above fields *)
  bindings : var_info SMap.t;
  local_bindings : var_info SMap.t;
  polymorphic : scheme SMap.t;
  subprotocols : subprotocol SMap.t;
}
[@@deriving show { with_path = false }, eq]

let empty_env =
  {
    parties = IMap.empty;
    types = IMap.empty;
    bindings = SMap.empty;
    local_bindings = SMap.empty;
    polymorphic = SMap.empty;
    subprotocols = SMap.empty;
  }

let pmeta ?(tid = { name = "main"; params = [] }) ~loc ~env () =
  { ploc = loc; tid; penv = env }

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

let party_list parties = parties |> IMap.values |> List.of_iter

type spec_decl =
  | Invariant of expr
  | Ltl of expr
  | Function of string * string list * protocol
  | SpecParty of {
      var : string;
      set : string;
      initial : (string * expr) list;
      size : int;
    }
[@@deriving show { with_path = false }]

type spec = {
  decls : spec_decl list;
  protocol : protocol;
}
[@@deriving show { with_path = false }]
