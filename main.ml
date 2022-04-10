open Syntax
open Eval

let _ = eval_program (empty_state Format.err_formatter) [
  TpDecl {
    name = "Nat";
    constructors = [{
      owner_name = "Nat";
      name = "Z";
      fields = [];
    }; {
      owner_name = "Nat";
      name = "Z";
      fields = [Named "Nat"];
    }]
  };
  TmDecl {
    name = "double";
    typ = Arrow (Named "Nat", Named "Nat");
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
    typ = Named "Nat";
    recursive = false;
    body = Some Sugar.(const "S" [const "S" [const "Z" []]]);
  };
  TmDecl {
    name = "four";
    typ = Named "Nat";
    recursive = false;
    body = Some Sugar.(r "double" @@@ r "two");
  };
  TmDecl {
    name = "halve";
    typ = Arrow (Named "Nat", Named "Nat");
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
    typ = Named "Nat";
    recursive = false;
    body = Some Sugar.(r "halve" @@@ r "four");
  };
]
