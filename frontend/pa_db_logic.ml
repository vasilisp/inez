open Camlp4
open Core.Std

exception Type_Exn of string

module Id : Sig.Id =
struct
  let name = "pa_db_logic"
  let version = "0.1"
end

module Make (Syntax : Sig.Camlp4Syntax) = struct

  open Sig

  module Name = struct let name = "Db_logic" end
  include Pa_logic_impl.Make(Name)(Syntax)

  let select_pattern _loc id tid =
    match id, tid with
    | Some id, "int" ->
      <:patt< Terminology.H_Int $lid:id$ >>
    | None, "int" ->
      <:patt< Terminology.H_Int _ >>
    | Some id, "bool" ->
      <:patt< Terminology.H_Bool $lid:id$ >>
    | None, "bool" ->
      <:patt< Terminology.H_Bool _ >>
    | _, _ ->
      Loc.raise _loc (Type_Exn ("unknown type: " ^ tid)) ;;

  (* FIXME : maybe there is a shorthand for this *)
  let patt_of_list _loc =
    List.fold_right ~init: <:patt< [] >>
      ~f:(fun p acc -> <:patt< p :: acc >>)

  let dbpatt = Gram.Entry.mk "dbpatt"

    EXTEND Gram

    dbpatt:
    [ [ id = LIDENT -> select_pattern _loc (Some id) "int" ]
    | [ "("; "_"; ":"; tid = LIDENT;
        ")" ->
        select_pattern _loc None tid ]
    | [ "("; id = LIDENT; ":"; tid = LIDENT;
        ")" ->
        select_pattern _loc (Some id) tid ] ];

    expr:
      LEVEL "top"
      [ [ "select"; db = expr;
          "where"; l = LIST1 dbpatt; "->"; e = expr ->
          let id = Pa_logic_impl.gensym () in
          <:expr<
            Db_logic.D.D_Sel
            ($db$, fun $lid:id$ ->
              match Db_logic.R.to_list $lid:id$ with
              | $patt_of_list _loc l$ -> $e$
              | _ -> Formula.F_Not Formula.F_True) >> ] ];

    END

end

module M = Register.OCamlSyntaxExtension(Id)(Make)
