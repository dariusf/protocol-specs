open Containers

type pos = {
  line : int;
  col : int;
}
[@@deriving show { with_path = false }, eq]

type loc = {
  start : pos;
  stop : pos;
}
[@@deriving show { with_path = false }, eq]

exception Check_failure of string

let fail ~loc s =
  Format.ksprintf
    ~f:(fun m ->
      raise
        (Check_failure
           (Format.sprintf "error at line %d, col %d:\n@[<h>%s@]" loc.start.line
              loc.start.col m)))
    s

let bad_input s =
  Format.ksprintf
    ~f:(fun m -> raise (Check_failure (Format.sprintf "bad input: %s" m)))
    s

let bug s = Format.ksprintf ~f:failwith s

let nyi s =
  Format.ksprintf
    ~f:(fun m -> failwith (Format.sprintf "not yet implemented: %s" m))
    s

let rec pairwise_foldr f init xs =
  match xs with
  | [] | [_] -> init
  | a :: b :: xs1 -> f a b (pairwise_foldr f init (b :: xs1))

(** https://hackage.haskell.org/package/base-4.14.1.0/docs/src/Data.Foldable.html#foldr1 *)
let foldr1 f xs =
  List.fold_right
    (fun c t -> match t with None -> Some c | Some d -> Some (f c d))
    xs None
  |> Option.get_exn_or "foldr1: empty"

let map_last f xs =
  let l = List.length xs in
  List.mapi (fun i x -> f (i = l - 1) x) xs

let rec transpose xss =
  match xss with
  | (_ :: _) :: _ -> List.map List.hd xss :: transpose (List.map List.tl xss)
  | _ -> []

let foldl1 f xs =
  match xs with
  | [] -> failwith "foldl1: empty"
  | x :: rest -> List.fold_left f x rest

let foldr1 f xs =
  match xs with
  | [] -> failwith "foldr1: empty"
  | x :: rest -> List.fold_right f rest x

module UF = UF.Int

module Printing = struct
  open PPrint

  let (arrow, disj, par, if_, when_, in_, forall, exists) =
    ( string "->",
      string "\\/",
      string "||",
      string "=>",
      string "=>*",
      string "in",
      string "forall",
      string "exists" )

  let spaced d = terminate space d

  let nl = break 1
end

let is_alpha = function 'a' .. 'z' | 'A' .. 'Z' -> true | _ -> false

let write_to_file ~filename content =
  IO.File.write_exn filename content;
  print_endline filename

let pp_const s fmt () = Format.fprintf fmt "%s" s

module List = struct
  include List

  let pp ?(start = "[") ?(stop = "]") ?(sep = "; ") e fmt l =
    pp ~pp_start:(pp_const start) ~pp_stop:(pp_const stop)
      ~pp_sep:(pp_const sep) e fmt l
end

module Pair = struct
  include Pair

  let pp ?(start = "(") ?(stop = ")") ?(sep = ", ") a b fmt l =
    pp ~pp_start:(pp_const start) ~pp_stop:(pp_const stop)
      ~pp_sep:(pp_const sep) a b fmt l
end

module String = struct
  include String

  let pp = Format.pp_print_string
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

module SSet = struct
  module M = Set.Make (String)
  include M

  let pp fmt map =
    Format.fprintf fmt "%a"
      (M.pp ~pp_sep:(pp_const ", ") ~pp_start:(pp_const "{")
         ~pp_stop:(pp_const "}") Format.pp_print_string)
      map
end

let snake_to_camel s =
  s |> String.lowercase_ascii |> String.capitalize_ascii
  |> Str.global_substitute (Str.regexp {|_\([a-z]\)|}) (fun s ->
         Str.matched_group 1 s |> String.lowercase_ascii
         |> String.capitalize_ascii)
