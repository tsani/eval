module E = Syntax.External

module State = struct
  type t = {
    here : Loc.t;
  }
end

module Env = struct
  type t = {
    input : string;
  }
end

module ParseError = struct
  type t
end

type 'a t = { run : 'r. Env.t -> State.t -> (ParseError.t -> 'r) -> (State.t -> 'a -> 'r) -> 'r }

let bind (p : 'a t) (k : 'a -> 'b t) : 'b t = {
  run = fun r s fail return -> p.run r s fail @@ fun s x -> (k x).run r s fail return
}

let map (f : 'a -> 'b) (p : 'a t) : 'b t = {
  run = fun r s fail return -> p.run r s fail @@ fun s x -> return s (f x)
}

(* Look at the character at the parser's current position. *)
let peek (p : 'a t) : char t = {
  run = fun r s fail return -> return s @@ String.get Env.(r.input) s.State.here.Loc.offset
}
