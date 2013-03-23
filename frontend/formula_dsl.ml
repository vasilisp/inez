open Camlp4
open Core.Std

exception Int_Exn

module Id : Sig.Id =
struct
  let name = "pa_logic"
  let version = "0.1"
end

module Make (Syntax : Sig.Camlp4Syntax) =
struct
  
  open Sig
  include Syntax

  let gensym =
    let cnt = ref 0 in
    fun ?(prefix = "_x") () ->
      incr cnt;
      sprintf "%s__%03i_" prefix !cnt

  let gen_function_id = gensym ~prefix:"f"

  let expr_of_list_ids _loc =
    List.fold_right
      ~init:<:expr< []>>
      ~f:(fun id acc -> <:expr< $id:id$ :: $acc$ >>)

  let expr_with_funs _loc init =
    List.fold_right ~init
      ~f:(fun id acc -> <:expr< fun $id:id$ -> $acc$ >>)

  let simplepatt = Gram.Entry.mk "simplepatt";;

  class ['a] logic_subst _loc = object
    inherit Ast.map as super
    method _Loc_t (_: 'a) = _loc
    method expr = function
    | <:expr< true >> ->
      <:expr< Formula.true' >>
    | <:expr< false >> ->
      <:expr< Formula.false' >>
    | <:expr< $int:s$ >> ->
      <:expr< Formula.of_int63 (Int63.of_string $str:s$) >>
    | <:expr< $int64:s$ >> ->
      <:expr< Formula.of_int63 (Int63.of_string $str:s$) >>
    | e -> super#expr e
  end;;

  EXTEND Gram

  simplepatt:
    [ [ "_" -> Ast.IdLid (_loc, gensym ()) ]
    | [ id = LIDENT -> Ast.IdLid (_loc, id) ] ];

  str_item:
    LEVEL "top" [
      [ "sort";
        id = LIDENT ->
        ignore id;
        let module_id = gensym ~prefix:"S_" () in
        <:str_item< module $uid:module_id$ =
                      (struct type t = unit end:
                         sig type t end) >>
      ]
    ];
  
  expr:
    LEVEL "top" [
      [ "uf";
        l = LIST1 simplepatt ->
        expr_with_funs _loc
          (let l = expr_of_list_ids _loc l in
           <:expr< Formula.app $str:gensym ~prefix:"f" ()$ $l$ >>) l
      | "logic"; "("; e = SELF;
        ")" -> let e = (new logic_subst _loc)#expr e in
               <:expr< Formula.(Formula.($e$)) >> ]
    ];

  END

end

module M = Register.OCamlSyntaxExtension(Id)(Make)
