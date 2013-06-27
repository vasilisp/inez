open Camlp4.PreCast
;;

type y = Y_Int | Y_Bool
;;

exception Unreachable of string
;;

(* Treating n-tuples as trees. Not sure whether they will always look
   like lists. *)

let irrefutable = function
  | <:patt< $lid:_$ >> | <:patt< _ >> ->
    true
  | _ ->
    false
;;

let cast_pattern = function
  | <:patt@loc< ($p$ : Int) >> when irrefutable p ->
    Some <:patt@loc< Terminology.H_Int $p$ >>
  | <:patt@loc< ($p$ : Bool) >> when irrefutable p ->
    Some <:patt@loc< Terminology.H_Bool $p$ >>
  | <:patt@loc< $lid:_$ >> as p ->
    Some <:patt@loc< Terminology.H_Int $p$ >>
  | <:patt< _ >> as p ->
    Some p
  | _ ->
    None
;;

let rec list_of_pattern = function
  | Ast.PaCom (_, p1, p2) ->
    (match list_of_pattern p1 with
    | Some l1 ->
      (match list_of_pattern p2 with
      | Some l2 ->
        Some (List.append l1 l2)
      | None ->
        None)
    | None ->
      None)
  | p ->
    match cast_pattern p with
    | Some p ->
      Some [p]
    | None ->
      None
;;

let list_of_pattern = function
  | <:patt< $lid:_$ >> | <:patt< _ >> as p ->
    Some [p]
  | Ast.PaTup (_, u) ->
    list_of_pattern u
  | _ ->
    None
;;

let pattern_of_list _loc =
  ListLabels.fold_right ~init:<:patt< [] >>
    ~f:(fun p acc -> <:patt< $p$ :: $acc$ >>)
;;

let transform_select = function
  | <:expr@loc< fun ($p$ : Row) -> $e'$ >> as e ->
    (match list_of_pattern p with
    | Some l ->
      (let p = pattern_of_list loc l
      and id = Camlp4_maps.gensym () in
       <:expr@loc<
         fun $lid:id$ ->
           match Db_logic.R.to_list $lid:id$ with
           | $p$ -> $e'$
           | _ ->
             Formula.(F_Not F_True) >>)
    | None ->
      e)
  | e ->
    e
;;

let map_select = Ast.map_expr transform_select
;;

let rec ylist_of_ctyp ?acc:(acc = []) = function
  | <:ctyp< Schema >> ->
    Some acc
  | <:ctyp< Int $c$ >> ->
    ylist_of_ctyp ~acc:(Y_Int :: acc) c
  | <:ctyp< Bool $c$ >> ->
    ylist_of_ctyp ~acc:(Y_Bool :: acc) c
  | _ ->
    None
;;

let gadt_param_of_y _loc = function
  | Y_Int ->
    <:ctyp< int >>
  | Y_Bool ->
    <:ctyp< bool >>
;;

let gadt_param_of_ylist _loc l =
  match List.rev l with
  | a :: d ->
    ListLabels.fold_left d
      ~init:(gadt_param_of_y _loc a)
      ~f:(fun acc y -> <:ctyp< $gadt_param_of_y _loc y$ * $acc$ >>)
  | _ ->
    raise (Unreachable "gadt_param_of_ylist")
;;

let gadt_param_str_item_of_ylist _loc id l =
  let ty = gadt_param_of_ylist _loc l in
  Ast.StTyp (_loc, (Ast.TyDcl (_loc, id, [], ty, [])))

let schema_expr_of_y _loc  = function
  | Y_Int ->
    <:expr< Db_logic.S.S_Int >>
  | Y_Bool ->
    <:expr< Db_logic.S.S_Bool >>
;;

let schema_expr_of_ylist _loc l =
  match List.rev l with
  | a :: d ->
    ListLabels.fold_left d
      ~init:(schema_expr_of_y _loc a)
      ~f:(fun acc y ->
        let e = schema_expr_of_y _loc y in
        <:expr< Db_logic.S.S_Pair ($e$, $acc$) >>)
  | _ ->
    raise (Unreachable "schema_expr_of_ylist")
;;

let make_column_expr _loc y id =
  match y with
  | Y_Int ->
    <:expr< Db_logic.R.R_Int $id:id$ >>
  | Y_Bool ->
    <:expr< Db_logic.R.R_Bool (Db_logic.M.M_Bool $id:id$) >>
;;

let make_row_expr_of_ylist _loc l =
  let l' =
    let f _ = Ast.IdLid (_loc, Camlp4_maps.gensym ()) in
    ListLabels.map l ~f in
  let f acc y a =
    let c = make_column_expr _loc y a in
    <:expr< Db_logic.R.R_Pair ($c$, $acc$) >> in
  match List.rev l, List.rev l' with
  | a :: d, a' :: d'  ->
    let init = make_column_expr _loc a a' in
    let body = ListLabels.fold_left2 d d' ~init ~f
    and p =
      let l' = ListLabels.map l' ~f:(fun id -> <:patt< $id:id$ >>) in
      Ast.PaTup (_loc, Ast.paCom_of_list l') in
    <:expr< fun $p$ -> $body$ >>
  | _ ->
    raise (Unreachable "make_row_expr_of_ylist")
;;

let make_row_str_item_of_ylist _loc id l =
  <:str_item< let $lid:"make_row_" ^ id$ =
                $exp:make_row_expr_of_ylist _loc l$ >>
;;

let make_db_expr_of_ylist _loc l =
  let s = schema_expr_of_ylist _loc l
  and i = Camlp4_maps.gensym () in
  <:expr< fun $lid:i$ -> Db_logic.D.D_Input ($s$, $lid:i$) >>
;;

let make_db_str_item_of_ylist _loc id l =
  <:str_item< let $lid:"make_db_" ^ id$ =
                $exp:make_db_expr_of_ylist _loc l$ >>
;;

let transform_schema_type = function
  | Ast.StTyp (_loc, (Ast.TyDcl (_, id, [], y, []))) as s ->
    (match ylist_of_ctyp y with
    | Some l ->
      let s1 = gadt_param_str_item_of_ylist _loc id l
      and s2 = make_row_str_item_of_ylist _loc id l
      and s3 = make_db_str_item_of_ylist _loc id l in
      Ast.StSem (_loc, s1, Ast.StSem (_loc, s2, s3))
    | None ->
      s)
  | (<:str_item@loc< let _ = () >>) ->
    <:str_item@loc< let a = () >>
  | s ->
    s
;;

let map_schema_type =
  Ast.map_str_item transform_schema_type
;;

let _ =
  let m = (Camlp4_maps.map_uf "Db_logic")#str_item in
  AstFilters.register_str_item_filter m;
  AstFilters.register_topphrase_filter m
;;

let _ =
  let m = (Camlp4_maps.map_logic "Db_logic")#str_item in
  AstFilters.register_str_item_filter m;
  AstFilters.register_topphrase_filter m
;;

let _ =
  let m = map_select#str_item in
  AstFilters.register_str_item_filter m;
  AstFilters.register_topphrase_filter m
;;

let _ =
  let m = map_schema_type#str_item in
  AstFilters.register_str_item_filter m;
  AstFilters.register_topphrase_filter m
;;
