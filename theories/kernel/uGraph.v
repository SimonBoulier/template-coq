Require Import BinInt List. Import ListNotations.
From Template Require Import univ.


(* For the moment we recompute the graph each time *)
Definition t : Type := LevelSet.t * Constraint.t.

(* FIXME for the moment Prop : Set *)
Definition init_graph : t :=
  let levels := LevelSet.add Level.prop (LevelSet.add Level.set LevelSet.empty) in
  let constraints := Constraint.add (Level.prop, Le, Level.set) Constraint.empty in
  (levels, constraints).

Definition add_constraints (uctx : universe_context) (G : t)
  := let levels := List.fold_left (fun s l => LevelSet.add l s) (fst uctx) (fst G) in
     let constraints := Constraint.union (snd uctx) (snd G) in
     (levels, constraints).


Section UGraph.
  Variable (φ : t).

  (* TODO use nat where Z is not useful or BinNat *)
  Local Open Scope Z.

  Definition edge : Set := Level.t * Z * Level.t.

  Definition edges_of_constraint (uc : univ_constraint) : list edge
    := let '((l, ct),l') := uc in
       match ct with
       | Lt => [(l,-1,l')]
       | Le => [(l,0,l')]
       | Eq => [(l,0,l'); (l',0,l)]
       end.

  (* FIXME duplicates *)
  Definition edges : list edge
    := Constraint.fold (fun uc E => edges_of_constraint uc ++ E) (snd φ) [].

  (* The graph *)
  (* For each node we record its predecessos  *)
  Definition pred_graph := LevelMap.t (Level.t * Z).

  Definition Zinfty := (Z.pow 2 6)%Z.  (* FIXME bigger at least *)

  Definition add_node l := LevelMap.add l (Level.Level "nil", Zinfty).

  Definition init_pred_graph : pred_graph :=
    LevelSet.fold add_node (fst φ) (LevelMap.empty _).

  Definition relax (G : pred_graph) (e : edge) : pred_graph :=
    let '((u, w), v) := e in
    match LevelMap.find u G, LevelMap.find v G with
    | Some (_, ud), Some (_, vd)
      => if Z.gtb vd (ud + w) then
          LevelMap.add v (u, ud + w) G
        else G
    | _, _ => G
    end.

  Definition BellmanFord (G : pred_graph) (s : Level.t) : pred_graph :=
    let G' := LevelMap.add s (Level.Level "nil", Z0) G in
    let G' := LevelMap.fold (fun _ _ => fold_left relax edges) G G' in
    G'.

  (* true if there is a negative cycle *)
  Definition detect_negative_cycle (G : pred_graph) : bool
    := existsb (fun '((u,w),v) =>
                  match LevelMap.find u G, LevelMap.find v G with
                  | Some (_, ud), Some (_, vd)
                    => Z.gtb vd (ud + w)
                  | _, _ => false
                  end) edges.

  (* If enforce l1 l2 = Some n, the graph enforce that l2 is at least l1 + n *)
  (* i.e. l1 + n <= l2 *)
  (* If None nothing is enforced by the graph between those two levels *)
  Definition enforce (u v : Level.t) : option Z :=
    let G := BellmanFord init_pred_graph u in
    match LevelMap.find v G with
    | Some (_, vd) => Some (Z.opp vd)
    | None => None
    end.

  Definition check_le_level_expr (e1 e2 : Universe.Expr.t) : bool :=
    match e1, e2 with
    | (l1, false), (l2, false)
    | (l1, true), (l2, true) => match enforce l1 l2 with
                               | Some k => Z.geb k 0
                               | _ => false
                               end
    | (l1, true), (l2, false) => match enforce l1 l2 with
                               | Some k => Z.geb k 1
                               | _ => false
                               end
    | (l1, false), (l2, true) => match enforce l1 l2 with
                               | Some k => Z.geb k (-1)
                               | _ => false
                               end
    end.

  Definition check_lt_level_expr (e1 e2 : Universe.Expr.t) : bool :=
    match e1, e2 with
    | (l1, false), (l2, false)
    | (l1, true), (l2, true) => match enforce l1 l2 with
                               | Some k => Z.geb k 1
                               | _ => false
                               end
    | (l1, true), (l2, false) => match enforce l1 l2 with
                               | Some k => Z.geb k 1
                               | _ => false
                               end
    | (l1, false), (l2, true) => match enforce l1 l2 with
                               | Some k => Z.geb k 0
                               | _ => false
                               end
    end.

  Definition check_eq_level_expr (e1 e2 : Universe.Expr.t) : bool :=
    check_le_level_expr e1 e2 && check_le_level_expr e2 e1.

  Definition exists_bigger_or_eq (e1 : Universe.Expr.t) (u2 : Universe.t) : bool :=
    Universe.existsb (check_le_level_expr e1) u2.

  Definition exists_strictly_bigger (e1 : Universe.Expr.t) (u2 : Universe.t) : bool :=
    Universe.existsb (check_lt_level_expr e1) u2.

  Definition check_leq (u1 u2 : Universe.t) : bool :=
    Universe.for_all (fun e => exists_bigger_or_eq e u2) u1.

  Definition check_lt (u1 u2 : Universe.t) : bool :=
    Universe.for_all (fun e => exists_strictly_bigger e u2) u1.

  (* true is all is ok *)
  Definition no_universe_inconsistency : bool :=
    let G := BellmanFord init_pred_graph Level.prop in
    negb (detect_negative_cycle G).

End UGraph.
