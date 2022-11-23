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
let next_line l = { l with offset = l.offset + 1; line = l.line + 1; column = l.column + 1 }

(* Increments offset and column keeping line unchanged. *)
let next_char l = { l with offset = l.offset + 1; column = l.column + 1 }

module Span = struct
  (* A span of text in a source file. *)
  type span = {
    start : t;
    stop : t;
  }

  type t = span

  (* A fake source span consists of fake locations. *)
  let is_fake { start; stop } = start = fake || stop = fake

  let fake = { start = fake; stop = fake }

  (* Joins two spans into a single one by taking the start of the first and the
  stop of the second. *)
  let join { start; } { stop; } = { start; stop }
end
