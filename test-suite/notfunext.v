Add ML Path "../src".
Add LoadPath "../theories" as Template.

Require Import Template.Template.
Require Import Template.Ast.

Axiom admit : forall {A}, A.
Tactic Notation "admit" := exact admit.

Require Import List.
Import ListNotations.
Open Scope type_scope.
Open Scope string_scope.


Notation "'Cheat'" := (tInd (mkInd "Coq.Init.Datatypes.bool" 0)).



Test Quote prod.
Notation "'mkProd'" := (tApp (tInd (mkInd "Coq.Init.Datatypes.prod" 0))).

Test Quote bool.
Notation "'mkBool'" := (tInd (mkInd "Coq.Init.Datatypes.bool" 0)).

Test Quote true.
Notation "'mkTrue'" := (tConstruct (mkInd "Coq.Init.Datatypes.bool" 0) 0).

Test Quote @pair.
Notation "'mkPair'" := (tApp (tConstruct (mkInd "Coq.Init.Datatypes.prod" 0) 0)).

Quote Recursively Definition f := @fst.
Notation "'mkFst'" := (ltac:(let t := eval compute in f in exact t)).
(* Notation "'mkFst'" := (tApp (tConst "Coq.Init.Datatypes.fst")). *)


Definition t1 := (mkProd [mkBool; mkBool]).

(* Make Definition t := ltac:(let x := cbn uconstr:(t1) in exact x). *)
Make Definition t := (mkProd [mkBool; mkBool]).
Make Definition t' := (mkPair [mkBool; mkBool; mkTrue; mkTrue]).

Fixpoint tsl (t : term) : term
  :=  match t with
      | tRel n => tRel n
      | tSort s => tSort s (* check with prop *)
      | tCast t k ty => tCast (tsl t) k (tsl ty)
      | tProd id ty t => mkProd [tProd id (tsl ty) (tsl t); mkBool]
      | tLambda id ty t => mkPair [tProd id (tsl ty) Cheat; mkBool; tLambda id (tsl ty) (tsl t) ; mkTrue]
      | tLetIn _ dfn ty t => admit
      | tApp fn args => tApp mkFst ((mkPair (mkBool :: mkBool :: mkTrue :: mkTrue :: nil)) :: nil)
      (* | tApp fn args => mkFst (Cheat :: Cheat :: (map tsl (fn :: args))) *)
      | tConst nm => tConst nm
      | tConstruct i n => tConstruct i n               
      | tCase _ ty mch brs => admit
      | tFix ds _ => admit
      | tInd i => tInd i
      | _ => admit
      end.

Definition mkImpl (A B : term) : term := tProd nAnon A B.

Definition tqsd' := Eval compute in (tsl (mkImpl mkBool mkBool)).

Quote Definition id_bool := fun b : bool => b.

Quote Definition test := (fun b : bool => b) true.
Compute (tsl test).
Make Definition qsdf :=
  ltac:(let t := eval compute in (tsl test) in exact t).

Print qsdf.