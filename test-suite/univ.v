From Template Require Import Ast Template.
Require Import String.

Open Scope string.


(* Set Universe Polymorphism. *)

Monomorphic Universe i j.
Definition test := (fun (T : Type@{i}) (T2 : Type@{j}) => T -> T2).
Set Printing Universes.
Print test.
Print Universes.
Unset Printing Universes. 

Quote Definition qtest := Eval compute in (fun (T : Type@{i}) (T2 : Type@{j}) => T -> T2).
Print qtest.

Make Definition bla := Eval compute in qtest.
Make Definition bla' := (tLambda (nNamed "T") (tSort ((Level.Level "Top.2", false) :: nil)%list) (tLambda (nNamed "T2") (tSort ((Level.Level "Top.1", false) :: nil)%list) (tProd nAnon (tRel 1) (tRel 1)))).

Set Printing Universes.
Print bla.
Print bla'.
Print Universes.
Unset Printing Universes.

Set Universe Polymorphism.

Section test.
  Universe u v.

  Definition t@{u v} : _ -> _ -> Type@{max(u,v)}:=  (fun (T : Type@{u}) (T2 : Type@{v}) => T -> T2).
  Set Printing Universes.
  Print t.

  
End test.

Compute t.
Compute (@t Type@{i} Type@{j}).
(* Compute (@t@{i j i j}). *)

Quote Definition qt := Eval compute in t.
Print qt.

Make Definition t' := Eval compute in qt.

Polymorphic Definition Funtp@{i} (A B: Type@{i}) := A->B.

Polymorphic Definition F@{i} := Type@{i}.

Quote Definition qT := Eval compute in F.
Require Import List. Import ListNotations.
Make Definition T' := (tSort [(Level.Var 1, false)]).

Quote Recursively Definition qT' := F.

Quote Definition qFuntp := Eval compute in Funtp.
Print qFuntp.
(** the same thing is quoted in demo.v using the template-coq monad
there the poly vars actually show up *)


Make Definition t2 := (Ast.tLambda (Ast.nNamed "T") (Ast.tSort (Ast.sType "Top.1"))
                                   (Ast.tLambda (Ast.nNamed "T2") (Ast.tSort (Ast.sType "Top.2")) (Ast.tProd Ast.nAnon (Ast.tRel 1) (Ast.tRel 1)))).
Set Printing Universes.
Print t2.
Print Universes.
