open Syntax
open Eval

let ty_nat = Named ("Nat", [])

let program = [
  TpDecl {
    name = "Nat";
    tvar_binders = [];
    constructors = [{
      owner_name = "Nat";
      name = "Z";
      fields = [];
    }; {
      owner_name = "Nat";
      name = "S";
      fields = [ty_nat];
    }]
  };
  TmDecl {
    name = "double";
    typ = mono @@ Arrow (ty_nat, ty_nat);
    recursive = true;
    body = Some begin let open Sugar in
      lam begin
        case (v 0) [
          pconst "Z" [] --> begin const "Z" [] end;
          pconst "S" [pv] --> begin
            const "S" [const "S" [r "double" @@@ v 0]]
          end
        ]
      end
    end;
  };
  TmDecl {
    name = "two";
    typ = mono @@ ty_nat;
    recursive = false;
    body = Some Sugar.(const "S" [const "S" [const "Z" []]]);
  };
  TmDecl {
    name = "four";
    typ = mono @@ ty_nat;
    recursive = false;
    body = Some Sugar.(r "double" @@@ r "two");
  };
  TmDecl {
    name = "halve";
    typ = mono @@ Arrow (ty_nat, ty_nat);
    recursive = true;
    body = Some begin let open Sugar in
      lam begin
        case (v 0) [
          pconst "Z" [] --> const "Z" [];
          pconst "S" [pconst "Z" []] --> const "Z" [];
          pconst "S" [pconst "S" [pv]] --> const "S" [r "halve" @@@ v 0];
        ]
      end
    end;
  };
  TmDecl {
    name = "half_of_four";
    typ = mono @@ ty_nat;
    recursive = false;
    body = Some Sugar.(r "halve" @@@ r "four");
  };
]

let r = Typecheck.check_program Signature.empty program

let _ = eval_program (State.empty Format.err_formatter) 
