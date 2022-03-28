open Containers

module Make (F : sig
  val name : string
end) =
struct
  let filename = F.name ^ ".txt"

  let file =
    IO.File.remove_noerr filename;
    IO.File.make filename

  let log fmt =
    Format.kasprintf (fun s -> IO.File.append_exn file (s ^ "\n")) fmt
end
