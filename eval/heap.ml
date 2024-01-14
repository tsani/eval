open RuntimeInfo

type addr = Int64.t

module Body = struct
    type t = value Array.t

    (** Writes values into the body starting at the given address. *)
    let write_at pos (l : value list) (body : t) : unit =
        List.iteri (fun i v -> body.(pos + i) <- v) l
end

module Runtime = struct
    type t = {
        body : Body.t;
        next_free : addr;
    }

    let make size = { body = Array.make size Int64.zero; next_free = 0L }

    (** Writes values at the next available address in the heap. Returns an adjusted runtime heap
        whose body has been mutated and in which the next free address is updated.
        Returns the address at which the values were written too. *)
    let write_next_free (values : value list) (r : t) : addr * t =
        (** Converts the heap object to a list of values. *)
        let a = r.next_free in
        Body.write_at (Int64.to_int r.next_free) values r.body;
        (a, { r with next_free = Int64.add r.next_free @@ Int64.of_int (List.length values) })
end

module Object = struct
    module Kind = struct
        type t =
            | CON
            | CLO
            | PAP
            | ARR

        let to_tag = function
            | CON -> '\x01'
            | CLO -> '\x02'
            | PAP -> '\x03'
            | ARR -> '\x04'

        let of_tag = function
            | '\x01' -> CON
            | '\x02' -> CLO
            | '\x03' -> PAP
            | '\x04' -> ARR
            | _ -> Util.invariant "[interpret] all tags are known"
    end

    module Header = struct
        type t = value

        let encode (k : Kind.t) (counts : int list) : t =
            if List.length counts > 7 then
                Util.invariant "[interpret] heap object header has at most 7 counts";
            let open Bytes in
            let b = make 8 '\x00' in
            set b 0 (Kind.to_tag k);
            List.iteri (fun i n -> set b (1 + i) (Char.chr n)) counts;
            get_int64_ne b 0

        let decode (hdr : t) : Kind.t * int list =
            (** Decomposes a value into 8 8-bit integers. *)
            let decompose_value (v : value) : char list =
                let b = Bytes.make 8 '\x00' in
                Bytes.set_int64_ne b 0 v;
                List.init 8 (fun i -> Bytes.get b i)
            in
            let tag :: counts = decompose_value hdr in
            (Kind.of_tag tag, List.map Char.code counts)
    end

    type con_spec = {
        tag : int;
        arity : int;
    }

    type clo_spec = {
        env_size : int;
        arity : int;
        body : code_addr;
    }

    type pap_spec = {
        held : int;
        missing : int;
        clo : addr;
    }

    type arr_spec = {
        capacity : int; (* count of 64-bit values *)
        length: int; (* count of bytes *)
    }

    type blob = value Array.t

    type spec =
        | Con of con_spec
        | Clo of clo_spec
        | Pap of pap_spec
        | Arr of arr_spec

    type obj = spec * blob

    (** Converts a heap object into a list of values, suitable for writing into a heap. *)
    let serialize (spec, blob) : value list = match spec with
        | Con { tag; arity } ->
            Header.(encode Kind.CON [tag; arity]) :: Array.to_list blob
        | Clo { env_size; arity; body } ->
            Header.(encode Kind.CLO [env_size; arity]) :: body :: Array.to_list blob
        | Pap { held; missing; clo } ->
            Header.(encode Kind.PAP [held; missing]) :: clo :: Array.to_list blob
        | Arr { capacity; length } ->
            Header.(encode Kind.ARR [capacity; length]) :: Array.to_list blob

    (** `load_blob pos heap spec` loads the array of values associated to the object with header
        `spec` located at position `pos` in `heap`. *)
    let load_blob (pos : addr) (heap : Body.t) : spec -> blob =
        let pos = Int64.to_int pos in
        function
        | Con { arity } -> Array.init arity (fun i -> heap.(pos + 1 + i))
        | Clo { env_size } -> Array.init env_size (fun i -> heap.(pos + 2 + i))
        | Pap { held } -> Array.init held (fun i -> heap.(pos + 2 + i))
        | Arr { capacity } -> Array.init capacity (fun i -> heap.(pos + 1 + i))

    (** Decodes a heap object from a heap at the given address. *)
    let load_spec (pos : addr) (heap : Body.t) : spec =
        let pos = Int64.to_int pos in
        match Header.decode heap.(pos) with
        | CON, tag :: arity :: _ -> Con { tag; arity }
        | CLO, env_size :: arity :: _ -> Clo { env_size; arity; body = heap.(pos + 1) }
        | PAP, held :: missing :: _ -> Pap { held; missing; clo = heap.(pos + 1) }
        | ARR, capacity :: length :: _ -> Arr { capacity; length }

    (** Calculates the size (as a count of values) of the given heap object. *)
    let size : spec -> int = function
        | Con { arity } -> 1 + arity
        | Clo { env_size } -> 2 + env_size
        | Pap { held; missing } -> 2 + held
        | Arr { capacity } -> 1 + capacity
        (* Everything gets a +1 for the header, then Clo and Pap get an extra +1 since they hold an
           address in addition to their fields. *)

    let as_clo = function
        | Clo spec -> spec
        | _ -> Util.invariant "[interpret] heap object must be a closure"

    let as_con = function
        | Con spec -> spec
        | _ -> Util.invariant "[interpret] heap object must be a constructor"

    let as_pap = function
        | Pap spec -> spec
        | _ -> Util.invariant "[interpret] heap object must be a partial application"

    let as_arr = function
        | Arr spec -> spec
        | _ -> Util.invariant "[interpret] heap object must be an array"
end
