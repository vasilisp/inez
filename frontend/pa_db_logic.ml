open Camlp4
open Core.Std

module Id : Sig.Id =
struct
  let name = "pa_db_logic"
  let version = "0.1"
end

module Name = struct let name = "Db_logic" end

module M =
  Register.OCamlSyntaxExtension(Id)(Pa_logic_impl.Make(Name))
