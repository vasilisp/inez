open Camlp4.PreCast

exception Type_Exn of string

(* Treating n-tuples as trees. Not sure whether they will always look
   like lists. *)

let irrefutable = function
  | <:patt< $lid:_$ >> | <:patt< _ >> ->
    true
  | _ ->
    false

let cast_pattern = function
  | <:patt@loc< ($p$ : Int) >> when irrefutable p ->
    Some <:patt@loc< Terminology.H_Int $p$ >>
  | <:patt@loc< ($p$ : Bool) >> when irrefutable p ->
    Some <:patt@loc< Terminology.H_Bool $p$ >>
  | p when irrefutable p ->
    let loc = Ast.loc_of_patt p in
    Some <:patt@loc< Terminology.H_Int $p$ >>
  | _ ->
    None

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

let list_of_pattern = function
  | <:patt< $lid:_$ >> | <:patt< _ >> as p ->
    Some [p]
  | Ast.PaTup (_, u) ->
    list_of_pattern u
  | _ ->
    None

let pattern_of_list _loc =
  ListLabels.fold_right ~init:<:patt< [] >>
    ~f:(fun p acc -> <:patt< $p$ :: $acc$ >>)

let transform_select = function
  | <:expr@loc< fun ($p$ : Row) -> $e'$ >> as e ->
    (match list_of_pattern p with
    | Some l ->
      let p = pattern_of_list loc l
      and id = Camlp4_maps.gensym () in
      <:expr@loc<
        fun $lid:id$ ->
          match Db_logic.R.to_list $lid:id$ with
          | $p$ -> $e'$
          | _ -> Formula.(F_Not F_True) >>
          | None ->
            e)
  | e ->
    e

let map_select = Ast.map_expr transform_select

let _ =
  let m = (Camlp4_maps.map_uf "Db_logic")#str_item in
  AstFilters.register_str_item_filter m;
  AstFilters.register_topphrase_filter m

let _ =
  let m = (Camlp4_maps.map_logic "Db_logic")#str_item in
  AstFilters.register_str_item_filter m;
  AstFilters.register_topphrase_filter m

let _ =
  let m = map_select#str_item in
  AstFilters.register_str_item_filter m;
  AstFilters.register_topphrase_filter m
