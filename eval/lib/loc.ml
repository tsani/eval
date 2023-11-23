(* A point in a file. Offset is zero-based. Line and column are one-based. *)
type t = {
  (* The total number of characters from the beginning *)
  offset : int; 
  (* The line the point is on *)
  line : int;
  (* The column the point is on *)
  column : int;
  (* The name of the file in which the location occurs. *)
  filename : string; 
}

let initial filename = { offset = 0; line = 1; column = 1; filename }

let fake = {
  offset = -1;
  line = -1;
  column = -1;
  filename = "<fake>"
}

let is_fake { offset; line; column; filename } = offset = -1 || line = -1 || column = -1 || filename = "<fake>"

(* Increments offset and line resetting column to 1 *)
let next_line l = { l with offset = l.offset + 1; line = l.line + 1; column = 1 }

(* Increases the offset and column of the location by the given count, keeping the line unchanged. *)
let bump n l = { l with offset = l.offset + n; column = l.column + n }

(* Increments the offset and column of the location, keeping line unchanged. *)
let next_char = bump 1

module Span = struct
  (* A span of text in a source file. *)
  type span = {
    start : t;
    stop : t;
  }

  let make (start : t) (stop : t) : span = { start; stop }

  type t = span

  type 'a d = t * 'a

  (* A fake source span consists of fake locations. *)
  let is_fake { start; stop } = start = fake || stop = fake

  let fake = { start = fake; stop = fake }

  (* Joins two spans into a single one by taking the start of the first and the
  stop of the second. *)
  let join s1 s2 = match () with
    | _ when is_fake s1 -> s2
    | _ when is_fake s2 -> s1
    | _ -> { start = s1.start; stop = s2.stop }
end

type span = Span.t

let print ppf { line; column; filename; offset = _ } =
  Format.fprintf ppf "%s:%d:%d" filename line column
