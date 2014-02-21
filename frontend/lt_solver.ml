open Core.Std
open Logic

module Make (Imt : Imt_intf.S_with_cut_gen) (I : Id.S) = struct

  type occ = Imt.Dvars.t list * int option ref

  type instantiator = Imt.Dvars.t list -> Imt.ivar Terminology.iexpr

  type axiom = occ Dequeue.t * instantiator

  module Theory_solver = struct

    type ctx = {
      mutable r_next_id : int;
      r_axioms_h        : axiom Int.Table.t;
      mutable r_level   : int;
    }

    let make_ctx () = {
      r_next_id  = 0;
      r_axioms_h = Int.Table.create ~size:128 ();
      r_level    = 0
    }

    module F

      (S : Imt_intf.S_cut_gen_access
       with type ivar := Imt.ivar
       and type bvar := Imt.bvar
       and type Dvars.t = Imt.Dvars.t) =

    struct

      let check r r' _ = true

      let backtrack ({r_axioms_h; r_level} as r) r' =
        assert (r_level >= 0);
        r.r_level <- r.r_level - 1;
        let f ~key ~data:(occs, _) =
          let f = function
            | (_, ({contents = Some level'} as reference)) ->
              if level' > r.r_level then reference := None
            | _ ->
              () in
          Dequeue.iter occs ~f in
        Hashtbl.iter r_axioms_h ~f

      let push_level r r' =
        r.r_level <- r.r_level + 1

      let generate_axiom_needed {r_level} r' = function
        | vars, {contents = None} ->
          let f v =
            match S.Dvars.get_lb_local r' v with
            | Some b ->
              Int63.(b >= zero)
            | None ->
              false in
          List.for_all vars ~f
        | _ ->
          false

      let generate_axiom r r' (occs, f : axiom) =
        (* FIXME: decide on bounds convention *)
        let found = ref false in
        let f ((vars, level : occ) as occ) =
          if generate_axiom_needed r r' occ then begin
            S.add_cut_local r' (f vars);
            level := Some r.r_level;  
          found := true
          end in
        Dequeue.iter occs ~f;
        !found

      let generate ({r_axioms_h} as r) r' =
        if
          let f ~key ~data acc = generate_axiom r r' data || acc
          and init = false in
          Hashtbl.fold r_axioms_h ~init ~f
        then
          `Ok
        else
          `Fail

    end

    let assert_axiom ({r_next_id = id; r_axioms_h} as r) f =
      r.r_next_id <- id + 1;
      Hashtbl.replace r_axioms_h id (Dequeue.create (), f)

    let assert_instance {r_axioms_h} id l =
      let occs, f = Hashtbl.find_exn r_axioms_h id in
      Dequeue.enqueue_back occs l

  end

  module Imt = Imt.F(Theory_solver)

  include Solver.Make(Imt)(I)

  let make_ctx () =
    make_ctx (Imt.make_ctx (Theory_solver.make_ctx ()))

  let assert_axiom = Theory_solver.assert_axiom

  let assert_instance = Theory_solver.assert_instance

end 
