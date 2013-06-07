open Camlp4
open Core.Std

exception Type_Exn of string

module Make

  (ModuleName : sig val name : string end)
  (Syntax : Sig.Camlp4Syntax) =

struct

  open Sig
  include Syntax

  type uf_type = Type.ibtype list * Type.ibtype

  let la _loc = <:module_expr< $uid:ModuleName.name$ >>

    let gensym =
      let cnt = ref 0 in
      fun ?(prefix = "_x") () ->
        incr cnt;
        sprintf "%s__%03i_" prefix !cnt

  let uf_ast_fun _loc (l, rtype) =
    let fold l init =
      let f acc = function
        | Type.E_Int ->
          <:expr< Type.Y_Int_Arrow $acc$ >>
        | Type.E_Bool ->
          <:expr< Type.Y_Bool_Arrow $acc$ >> in
      List.fold_left l ~f ~init
    and ret e =
      <:expr< $uid:ModuleName.name$.M.M_Var (gen_id $e$) >> in
    match rtype with
    | Type.E_Int ->
      ret (fold l <:expr< Type.Y_Int >>)
    | Type.E_Bool ->
      ret (fold l <:expr< Type.Y_Bool >>)

  let uf_ast_apps _loc init =
    List.fold2_exn ~init
      ~f:(fun acc id t ->
        let t =
          match t with
          | Type.E_Int ->
            <:expr< $id:id$ >>
          | Type.E_Bool ->
            <:expr< $uid:ModuleName.name$.M.M_Bool $id:id$ >> in
        <:expr< $uid:ModuleName.name$.M.M_App ($acc$, $t$) >>)

  let uf_ast_mlfun _loc init =
    List.fold_right ~init
      ~f:(fun id acc -> <:expr< fun $id:id$ -> $acc$ >>)

  let ground_type_of_id _loc = function
    | "int" ->
      Type.E_Int
    | "bool" ->
      Type.E_Bool
    | id ->
      Loc.raise _loc (Type_Exn ("unknown type: " ^ id))

  let uf_maybe_convert _loc r e =
    match r with
    | Type.E_Bool ->
      <:expr< Formula.F_Atom ($uid:ModuleName.name$.A.A_Bool ($e$))
      >>
    | Type.E_Int ->
      e

  let uf_ast _loc l_types r =
    let l_ids =
      let f _ = Ast.IdLid (_loc, gensym ()) in
      List.map l_types ~f
    and r_type = ground_type_of_id _loc r
    and id = gensym ~prefix:"__uf_" () in
    let inside =
      uf_ast_mlfun _loc
        (uf_maybe_convert _loc r_type
           (uf_ast_apps _loc <:expr< $lid:id$ >> l_ids l_types))
        l_ids
    and binding = uf_ast_fun _loc (l_types, r_type) in
    <:expr< let $lid:id$ = $binding$ in $inside$ >>;;

  let subst_obj _loc = object
      
    inherit Ast.map as super
      
    method _Loc_t (_: 'a) = _loc
      
    method expr = function
    | <:expr< true >> ->
      <:expr< Formula.true' >>
    | <:expr< false >> ->
      <:expr< Formula.false' >>
    | <:expr< $int:s$ >> ->
      <:expr<
        $uid:ModuleName.name$.M.of_int63 (Int63.of_string $str:s$)
      >>
    | <:expr< $int64:s$ >> ->
      <:expr<
        $uid:ModuleName.name$.M.of_int63 (Int63.of_string $str:s$)
      >>
    | e ->
      super#expr e
        
  end;;

let lpatt = Gram.Entry.mk "lpatt"

  EXTEND Gram

  (* "limited pattern" *)
  lpatt:
  [ [ "("; "_"; ":"; tid = LIDENT; ")" ->
  ground_type_of_id _loc tid
    ]
  | [ "("; _ = LIDENT; ":"; tid = LIDENT; ")" ->
  ground_type_of_id _loc tid
    ] ];

  expr:
    LEVEL "top" [
      [ "logic"; "in"; e = expr LEVEL ";" ->
      let e = (subst_obj _loc)#expr e in
      <:expr< $uid:ModuleName.name$.Ops.($e$) >>
      | "uf"; l = LIST1 lpatt; "->"; r = LIDENT ->
      uf_ast _loc l r
      ] ];

  END

end
