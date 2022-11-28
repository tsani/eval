(* ***** Parser combinator library ***** *)

let is_whitespace c = c = ' ' || c = '\t' || c = '\n'
let is_lowercase c = c = Char.lowercase_ascii c
let is_uppercase c = c = Char.uppercase_ascii c
let is_letter c =
  let i = Char.code c in
  Char.code 'A' <= i && i <= Char.code 'Z'
  ||
  Char.code 'a' <= i && i <= Char.code 'z'

let is_digit c =
  let i = Char.code c in
  Char.code '0' <= i && i <= Char.code '9'

let is_symbol c =
  List.mem c ['!'; '@'; '#'; '$'; '%'; '^'; '&'; '*'; '<'; '>'; '|'; '/'; '\\'; '?'; '-']

type 'a susp = unit -> 'a
let delay x = fun () -> x
let force f = f ()

module State = struct
  type t = {
    here : Loc.t;
  }

  let map_loc (f : Loc.t -> Loc.t) (s : t) : t =
    { s with here = f s.here }

  let initial filename = {
    here = Loc.initial filename;
  }
end

module Env = struct
  type t = {
    input : string;
    backtrack : bool;
  }

  let make input = {
    input;
    backtrack = false;
  }
end

type parser_label =
  | Anon
  | Label of string
  | OneOf of parser_label list

module ParseError = struct
  type content =
    | WrongLiteral of { expected : string; actual : string }
    | Unsatisfied
    | NoMoreChoices
    | NotFollowedBy of parser_label

  (** A fatal error occurs when a parser fails after having consumed input. *)
  type t = Loc.t * [ `fatal | `non_fatal ] * content

  let make l fatality content = (l, fatality, content)
end

type 'a t = {
  label : parser_label;
  run : 'r. Env.t -> State.t -> (ParseError.t -> 'r) -> (State.t -> 'a -> 'r) -> 'r;
}

(** Labels the given parser exactly. *)
let label' label p = {
  p with label
}

(** Labels the given parser with a string. *)
let label label p = label' (Label label) p

(** Obtains the current parser position. *)
let here : Loc.t t = {
  label = Anon;
  run = fun r s fail return -> return s s.State.here
}

(** Runs `p' with unlimited backtracking enabled. *)
let trying (p : 'a t) : 'a t = {
  label = Anon;
  run = fun r s fail return -> p.run { r with backtrack = true } s fail return
}

(** Runs a parser and checks whether it failed.
    This even allows recovering from fatal errors. *)
let handle (p : 'a t) : (ParseError.t, 'a) Result.t t = {
  label = Anon;
  run = fun r s fail return -> p.run r s
      (fun e -> return s @@ Result.Error e)
      (fun s x -> return s @@ Result.Ok x)
}

let pure (x : 'a) : 'a t = {
  label = Anon;
  run = fun r s fail return -> return s x
}

let bind (p : 'a t) (k : 'a -> 'b t) : 'b t = {
  label = Anon;
  run = fun r s fail return -> p.run r s fail @@ fun s x -> (k x).run r s fail return
}

(** Causes a parser error at the given location. *)
let fail_at (loc : Loc.t) (e : ParseError.content) : 'a t = {
  label = Anon;
  run = fun r s fail return -> fail @@ ParseError.make loc (if r.backtrack then `non_fatal else `fatal) e
}

(* Causes a parser error at the current location. *)
let fail (e : ParseError.content) : 'a t =
  bind here @@ fun loc -> fail_at loc e

let (&>) (p1 : 'a t) (p2 : 'b t) : 'b t =
  bind p1 @@ fun _ -> p2

let (<&) (p1 : 'a t) (p2 : 'b t) : 'a t =
  bind p1 @@ fun x ->
  bind p2 @@ fun _ ->
  pure x

let map (f : 'a -> 'b) (p : 'a t) : 'b t = {
  label = Anon;
  run = fun r s fail return -> p.run r s fail @@ fun s x -> return s (f x)
}

(** Slightly specialized form of {!handle}.
    The failure must be non-fatal. Any failure can be made non-fatal with
    {!trying} *)
let optional (p : 'a t) : 'a option t =
  bind (handle p) @@ function
  | Result.Error (_, `non_fatal, _) -> pure None
  | Result.Ok x -> pure (Some x)

(** `many p' parses `p' zero or more times.
    WARNING: `many p' for a parser `p' that succeeds consuming no input usually
    leads to an infinite loop. *)
let rec many (p : 'a t) : 'a list t =
  bind (optional p) @@ function
  | None -> pure []
  | Some x -> bind (many p) @@ fun xs -> pure @@ x :: xs

(** `some p' parses `p' one or more times.
    WARNING: `some p' for a `p' that succeeds by consuming no input usually
    leads to an infinite loop. *)
let some (p : 'a t) : 'a list t =
  bind p @@ fun x ->
  bind (many p) @@ fun xs ->
  pure @@ x :: xs

(** `sep_by1 sep p' parses `p', one or more times, with `sep' between each. *)
let sep_by1 sep p =
  bind p @@ fun x ->
  bind (many (sep &> p)) @@ fun xs ->
  pure (x :: xs)

(** `sep_by0 sep p' parses `p', zero or more times, with `sep' between each. *)
let sep_by0 sep p =
  (optional @@ sep_by1 sep p) |> map begin function
    | None -> pure []
    | Some xs -> pure xs
  end

(** Runs `p1'. If it fails without consuming input, runs `p2'.
    If `p1' fails while consuming input, `p2' is not run.
*)
let alt (p1 : 'a t susp) (p2 : 'a t susp) : 'a t =
  bind here @@ fun Loc.({ offset }) ->
  bind (handle @@ force p1) @@ function
  | Result.Ok x -> pure x
  | Result.Error (l, _, _) when Loc.Span.(l.offset) = offset -> p2 ()
  | Result.Error (_, `non_fatal, _) -> p2 ()
  | Result.Error (l, fatality, e) -> fail_at l e

let choice (ps : 'a t susp list) : 'a t =
  force @@ List.fold_right (fun p acc -> delay @@ alt p acc) ps (fun () -> fail @@ ParseError.NoMoreChoices)

(* Look at the character at the parser's current position. *)
let peek : char t = {
  label = Anon;
  run = fun r s fail return -> return s @@ String.get Env.(r.input) s.State.here.Loc.offset
}

(* Advances the parser state by one character. *)
let next_char : unit t = {
  label = Anon;
  run = fun r s fail return -> return (State.map_loc Loc.next_char s) ()
}

(* Advances the parser state by one line.
   Must only be called when the character in consideration is a newline. *)
let next_line : unit t = {
  label = Anon;
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

(** Parses the character given exactly. *)
let char (c : char) : char t =
  label ("`" ^ String.make 1 c ^ "' character") @@
  satisfy (fun x -> x = c)

(* Parses the string given exactly.
   This is done efficiently by simply extracting a substring from the input,
   versus checking one character at a time using `satisfy'.
   The given string must not include any newline characters.
 *)
let string (str : string) : string t =
  let len = String.length str in {
    label = Label ("literal string `" ^ str ^ "'");
    run = fun r s fail return ->
      let from_input = String.sub r.Env.input s.State.here.Loc.offset len in
      if str = from_input then return (State.map_loc (Loc.bump len) s) str else
        fail @@ ParseError.(make s.State.here `non_fatal @@ WrongLiteral { expected = str; actual = from_input })
  }

(* `p1 |> not_followed_by p2` parses p1 provided that parsing p2 fails after it. *)
let not_followed_by (pr : 'a t) (pl : 'b t) : 'b t =
  bind pl @@ fun x ->
  bind (optional pr) @@ function
  | None -> pure x
  | Some _ -> fail @@ ParseError.NotFollowedBy pr.label

(* ***** Simple token parsers ***** *)

let both f g x = f x && g x
let either f g x = f x || g x
let all fs = List.fold_right both fs (fun _ -> true)
let any fs = List.fold_right either fs (fun _ -> false)
let letter = satisfy is_letter
let lchar = satisfy (both is_letter is_lowercase)
let uchar = satisfy (both is_letter is_uppercase)
let alphanumeric = satisfy (any [is_letter; is_digit; is_symbol])
let whitespace = satisfy is_whitespace
let digit = satisfy is_digit |> map (fun x -> String.make 1 x |> int_of_string)
let lparen = string "("
let rparen = string ")"
let raw_number =
  some digit |>
  map (fun ds -> List.fold_right (fun d (acc, pow10) -> (acc + d * pow10, pow10 * 10)) ds (0, 1)) |>
  map fst
let symbol = satisfy is_symbol

(* Parses a sequence of alphanumeric characters beginning with an uppercase letter. *)
let uword : string t =
  label "word beginning with uppercase letter" @@
  bind uchar @@ fun c ->
  bind (many alphanumeric) @@ fun cs ->
  pure (String.of_seq @@ List.to_seq @@ c :: cs)

(* Parses a sequence of alphanumeric characters beginning with a lowercase letter. *)
let lword : string t =
  label "word beginning with lowercase letter" @@
  bind lchar @@ fun c ->
  bind (many alphanumeric) @@ fun cs ->
  pure (String.of_seq @@ List.to_seq @@ c :: cs)

(** Parses `p' followed possibly by some whitespace. *)
let lexeme (p : 'a t) =
  p <& many whitespace

let number = lexeme (span raw_number)
let uident = lexeme (span uword)
let lident = lexeme (span lword)

(** Parses a literal string ensuring that it isn't isn't a prefix of a bigger symbol. *)
let symbol s = lexeme (span @@ string s) |> not_followed_by symbol
let sym_arrow = symbol "->"
let sym_pipe = symbol "|"
let sym_eq = symbol "="

(** Parses a literal string ensuring that that string isn't a prefix of a bigger word. *)
let keyword s = lexeme (span @@ string s) |> not_followed_by alphanumeric

let kw_let = keyword "let"
let kw_fun = keyword "fun"
let kw_in = keyword "in"
let kw_match = keyword "match"
let kw_rec = keyword "rec"
let kw_with = keyword "with"

let between start stop p =
  start &> p <& stop

let parenthesized p = lexeme (between lparen rparen p)

(* ***** Complex syntax parsers ***** *)

open Syntax.External

let rec typ () : Type.t t =
  let named () =
    label "named type" @@
    bind uident @@ fun (loc, a) ->
    bind (many @@ force typ) @@ fun ts ->
    pure @@ Type.Named (loc, a, ts)
  in
  let tvar () =
    label "type variable" @@
    bind lident @@ fun (loc, a) ->
    pure @@ Type.TVar (loc, a)
  in
  let atomic = label "atomic type" @@ choice [named; tvar] in
  bind atomic @@ fun t ->
  bind (optional sym_arrow) @@ function
  | None -> pure t
  | Some _ ->
    bind (force typ) @@ fun t' ->
    pure Type.(Arrow (Loc.Span.join (loc_of_tp t) (loc_of_tp t'), t, t'))

let rec pattern () : Term.pattern t =
  let wildcard () =
    label "wildcard pattern" @@
    lexeme (span @@ string "_") |> map (fun (loc, _) -> Term.WildcardPattern loc)
  in
  let variable () =
    label "variable pattern" @@
    lident |> map (fun (loc, x) -> Term.VariablePattern (loc, x))
  in
  let num () =
    label "integer literal pattern" @@
    number |> map (fun (loc, n) -> Term.NumPattern (loc, n))
  in
  let const () =
    label "constructor pattern" @@
    bind uident @@ fun (loc, ctor_name) ->
    bind (many @@ force pattern) @@ fun ps ->
    let loc = List.fold_left (fun acc p -> Loc.Span.join acc @@ Term.loc_of_pattern p) loc ps in
    pure Term.(ConstPattern (loc, ctor_name, ps))
  in
  choice [wildcard; variable; num; const; fun () -> parenthesized (force pattern)]

let rec last (l : 'a list) (return : 'a -> 'r) (fail : unit -> 'r) : 'r = match l with
  | [] -> fail ()
  | [x] -> return x
  | _ :: xs -> last xs return fail

let rec term () : Term.t t =
  let num () =
    label "integer literal" @@
    lexeme number |> map (fun (loc, n) -> Term.Num (loc, n))
  in
  let variable () =
    label "variable" @@
    lident |> map (fun (loc, x) -> Term.Var (loc, x))
  in
  let lam () =
    label "function literal" @@
    bind kw_fun @@ fun (loc_fun, _) ->
    bind lident @@ fun (loc_x, x) ->
    bind sym_arrow @@ fun _ ->
    bind (force term) @@ fun body ->
    let loc = Loc.Span.(join loc_fun @@ Term.loc_of_tm body) in
    pure @@ Term.Fun (loc, (loc_x, x), body)
  in
  let let_ () =
    label "let-expression" @@
    bind kw_let @@ fun (loc_let, _) ->
    bind (optional kw_rec) @@ fun rec_opt ->
    bind lident @@ fun (loc_x, x) ->
    bind sym_eq @@ fun _ ->
    bind (force term) @@ fun e1 ->
    bind kw_in @@ fun _ ->
    bind (force term) @@ fun e2 ->
    pure @@ Term.Let (
      Loc.Span.join loc_let @@ Term.loc_of_tm e2,
      Syntax.(if rec_opt = None then NonRec else Rec),
      (loc_x, x),
      e1,
      e2
    )
  in
  let match_ () =
    let case =
      label "match case" @@
      bind sym_pipe @@ fun (loc_pipe, _) ->
      bind (force pattern) @@ fun pat ->
      bind sym_arrow @@ fun _ ->
      bind (force term) @@ fun e ->
      pure @@ Term.Case (Loc.Span.join loc_pipe @@ Term.loc_of_tm e, pat, e)
    in
    label "match-expression" @@
    bind kw_match @@ fun (loc_match, _) ->
    bind (force term) @@ fun e ->
    bind kw_with @@ fun (loc_with, _) ->
    bind (many case) @@ fun cases ->
    pure @@ Term.Match (
      Loc.Span.join loc_match @@ last cases Term.(fun case -> case_body case |> loc_of_tm) (fun () -> loc_with),
      e,
      cases
    )
  in
  let const () =
    bind uident @@ fun (loc_const, ctor_name) ->
    bind (many @@ force term) @@ fun spine ->
    pure @@ Term.Const (
      Loc.Span.join loc_const @@ last spine Term.loc_of_tm (fun () -> loc_const),
      ctor_name,
      spine
    )
  in
  let term1 = choice [let_; match_; lam; num; variable; const; fun () -> parenthesized @@ force term] in
  bind term1 @@ fun e ->
  bind (optional @@ force term) @@ function
  | None -> pure e
  | Some e' -> pure Term.(App (Loc.Span.join (loc_of_tm e) (loc_of_tm e'), e, e'))
