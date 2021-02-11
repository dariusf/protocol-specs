open Containers
open Format

type 'a msgf = (('a, formatter, unit) format -> 'a) -> unit

let block ~(enter : 'a msgf) ~(content : 'b msgf) ?(exit : 'c msgf option) fmt =
  (* printing (in a vbox) outside this opening box will add indentation to the entire box *)
  fprintf fmt "@[<v 0>";
  (* open_vbox 0; *)
  enter
  @@ (* Format.printf ("@[" ^^ fmt ^^ "@]"); *)
  fprintf fmt;
  (* print_break 0 2; *)
  (* open_box 0; *)
  fprintf fmt "@;<0 2>@[";
  content @@ fprintf fmt;
  fprintf fmt "@]";
  match exit with
  | Some e ->
    fprintf fmt "@,";
    e @@ fprintf fmt;
    fprintf fmt "@]"
  | None -> fprintf fmt "@]"

let pblock ~enter ~content ?exit () = block ~enter ~content ?exit Format.stdout

let string f =
  f Format.str_formatter;
  let s = Format.flush_str_formatter () in
  s

(** this doesn't compose very well; string + block is probably the way to go *)
let sblock ~enter ~content ?exit () =
  string (fun fmt -> block fmt ~enter ~content ?exit)

(* Format.str_formatter; *)
(* let s = Format.flush_str_formatter () in *)
(* s *)

(* close_box (); *)
(* close_box () *)

let b () =
  pblock
    ~enter:(fun m -> m "lol")
    ~content:(fun _ ->
      pblock
        ~enter:(fun m -> m "haha")
        ~content:(fun m -> m "hur")
        ~exit:(fun m -> m "}")
        ())
    ()

let c () =
  print_endline "abc";
  sblock ~enter:(fun m -> m "lol") ~content:(fun m -> m "haha") ()
  |> print_endline;
  print_endline "def"

(* let a = "@[<v 0>a@;<0 2>@[b@]@]" *)
