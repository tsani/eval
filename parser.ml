module E = Syntax.External

module State = struct
  type t = {
    here : Loc.t;
  }

  let map_loc (f : Loc.t -> Loc.t) (s : t) : t =
    { s with here = f s.here }
end

module Env = struct
  type t = {
    input : string;
  }
end

module ParseError = struct
  type content =
    | WrongLiteral of { expected : string; actual : string }
    | Unsatisfied

  type t = Loc.t * content

  let make l content = (l, content)
end

type 'a t = { run : 'r. Env.t -> State.t -> (ParseError.t -> 'r) -> (State.t -> 'a -> 'r) -> 'r }

(** Obtains the current parser position. *)
let here : Loc.t t = {
  run = fun r s fail return -> return s s.State.here
}

let pure (x : 'a) : 'a t = {
  run = fun r s fail return -> return s x
}

(* Causes a parser error at the current location. *)
let fail (e : ParseError.content) : 'a t = {
  run = fun r s fail return -> fail @@ ParseError.make s.State.here e
}

let bind (p : 'a t) (k : 'a -> 'b t) : 'b t = {
  run = fun r s fail return -> p.run r s fail @@ fun s x -> (k x).run r s fail return
}

let (&>) (p1 : 'a t) (p2 : 'b t) : 'b t =
  bind p1 @@ fun _ -> p2

let map (f : 'a -> 'b) (p : 'a t) : 'b t = {
  run = fun r s fail return -> p.run r s fail @@ fun s x -> return s (f x)
}

(* Look at the character at the parser's current position. *)
let peek : char t = {
  run = fun r s fail return -> return s @@ String.get Env.(r.input) s.State.here.Loc.offset
}

(* Advances the parser state by one character. *)
let next_char : unit t = {
  run = fun r s fail return -> return (State.map_loc Loc.next_char s) ()
}

(* Advances the parser state by one line.
   Must only be called when the character in consideration is a newline. *)
let next_line : unit t = {
  run = fun r s fail return -> return (State.map_loc Loc.next_line s) ()
}

(* Consumes and returns the character at the current position if it satisfies a predicate. *)
let satisfy (p : char -> bool) : char t =
  bind peek @@ fun c ->
  match () with
  | _ when not (p c) -> fail ParseError.Unsatisfied
  | _ when c = '\n' -> next_line &> pure c
  | _ -> next_char &> pure c

(* Runs a parser and returns its result together with the span of source material traversed by it. *)
let span (p : 'a t) : (Loc.Span.t * 'a) t =
  bind here @@ fun start ->
  bind p @@ fun x ->
  bind here @@ fun stop ->
  pure (Loc.Span.make start stop, x)

(* Parses the string given exactly.
   This is done efficiently by simply extracting a substring from the input,
   versus checking one character at a time using `satisfy'.
   The given string must not include any newline characters.
 *)
let string (str : string) : string t =
  let len = String.length str in {
    run = fun r s fail return ->
      let from_input = String.sub r.Env.input s.State.here.Loc.offset len in
      if str = from_input then return (State.map_loc (Loc.bump len) s) str else
        fail @@ ParseError.(make s.State.here @@ WrongLiteral { expected = str; actual = from_input })
  }
