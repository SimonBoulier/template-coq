(* -*- coq-prog-args : ("-debug" "-type-in-type") -*-  *)

(* (* Is is necessary to import Template.trad for the definition of prod' *) *)
(* Require Import Template.Translation Template.trad. *)

(* Let T := Type. *)
(* Check (T : T). *)

(* Translate prod'. *)
(* Translate pair'. *)
(* (* Translate fst'. *) *)
(* (* Translate snd'. *) *)
(* Translate bool. *)
(* Translate true. *)
(* Translate false. *)

(* Definition n : (fun x => x) Type := nat. *)

(* Definition g := prod Prop Type. *)
(* Definition f := g. *)

(* Axiom tr : nat. *)

(* (* Fail Translate tr. *) *)
(* Translate g. *)
(* Translate f. *)
(* Print fᵗ. *)

(* Implement t2 : bool as totot. *)
(* econstructor. *)
(* Defined. *)
(* Print t2. *)
(* Print totot. *)

(* Definition t4 := (t2, true). *)
(* Translate t4. *)

(* Implement t3 : t2 = t2. *)
(* econstructor. *)
(* Defined. *)

(* Definition t3' := pair' _ _ t3 nat. *)
(* Translate t3'. *)
(* Print t3'ᵗ. *)

(* Implement nnnn : (nat -> nat). *)
(* (* Implement nnnn : prod' (nat -> nat) bool. *) *)
(* econstructor; econstructor. *)
(* Defined. *)

(* Set Printing Universes. *)

(* Definition t5 := forall X:Set, X. *)
(* (* Print Sorted Universes. *) *)
(* Translate t5. *)
(* Print Sorted Universes. *)

(* (* Axiom a : forall X, X. *) *)

(* Implement y : forall X:Set, X. *)
(* (* Print Sorted Universes. *) *)
(* refine (pair' _ _ _ _). *)
(* admit. econstructor. *)
(* Admitted. *)

(* Translate nat. *)
(* Translate unit. *)

(* Definition t := (fun x : nat => x). *)
(* Translate t.  *)

(* (* Set Primitive Projections. *) *)
(* (* Record prod' (A B : Set) : Set := *) *)
(* (*   pair' { fst' : A ; snd' : B }. *) *)
(* (* Arguments fst' {A B} _. *) *)
(* (* Arguments snd' {A B} _. *) *)

(* (* Translate prod'. *) *)
(* Definition mm := (pair' _ _ true tt).(fst'). *)
(* Translate mm. *)
(* Eval compute in mmᵗ. *)

(* (* Require Import BoolProd. *) *)

(* (* Declare ML Module "mTranslate". *) *)
(* (* Open Scope my_scope. *) *)


(* Tactic Notation "intro'" ident(X) := econstructor; [intro X|exact true]. *)
(* Tactic Notation "intros'" := repeat (refine (_, true); intro). *)
(* Tactic Notation "specialize'" hyp(H) uconstr(t) := apply fst' in H; specialize (H t). *)

(* Translate False. *)
(* Translate eq. *)

(* (* This translation allow to implement the negation of funext. *) *)
(* (* Test Quote  *) *)
(* Implement notFunext : *)
(*   ((forall (A B : Set) (f g : A -> B), (forall x:A, f x = f x) -> f = g) -> False). *)
(* Proof. *)
(*   intro' H. *)
(*   specialize' H unit. *)
(*   specialize' H unit. *)
(*   specialize' H (pair' _ _ (fun x => x) true). *)
(*   specialize' H (pair' _ _ (fun x => x) false). cbn in *. *)
(*   specialize' H (pair' _ _ (fun x => eq_refl) true). *)
(*   apply (f_equal snd') in H; cbn in H. *)
(*   discriminate H. *)
(* Defined. *)

(* (* (* A more constructive version on inhabited types. *) *) *)
(* (* Implement notFunext' : forall (A B : Type), *) *)
(* (*     B -> {f : A -> B & { g : A -> B & ((forall x, f x = g x) -> f = g) -> False}}. *) *)
(* (* Proof. *) *)
(* (*   intro' A. intro' B. intro' y. *) *)
(* (*   pose (f := fun _ : A => y). exists (f, true). exists (f, false). *) *)
(* (*   intro' H. *) *)
(* (*   specialize' H (fun x => eq_refl, true). *) *)
(* (*   apply (f_equal snd) in H; cbn in H. *) *)
(* (*   discriminate H. *) *)
(* (* Defined. *) *)


(* (* Check notFunext'. *) *)
(* (* Compute notFunext'ᶠ. *) *)


(* (* Definition notFunext'Nat := notFunext' nat nat. *) *)

(* (* (* If we want to prove some result about notFunext'Nat we first hae to extend the translation to it. *) *) *)
(* (* Translate notFunext'Nat. *) *)

(* (* (* Now we can postulate new principles about notFunext'Nat, always preserving consistency. *) *) *)
(* (* Implement notFunext'Nat01 : notFunext'Nat 0 = notFunext'Nat 1 -> False. *) *)
(* (* Proof. *) *)
(* (*   compute. refine (_, true). intro H. *) *)
(* (*   pose proof (f_equal (@projT1 _ _) H); cbn in *. *) *)
(* (*   apply (f_equal fst) in H0; cbn in *. *) *)
(* (*   assert ((fun _ : nat => 0) 0 = (fun _ : nat => 1) 0). *) *)
(* (*   change ((fun _ : nat => 0) 0 = (fun _ : nat => 1) 0). rewrite H0. reflexivity. *) *)
(* (*   discriminate H1. *) *)
(* (* Defined. *) *)



(* (* ** Some check of the translation on other types. *** *) *)

(* Implement f : forall (f : Type -> Type), f Type. *)
(* Abort. *)

(* Implement foo : forall A B : Type, forall (f g : A -> B), forall x, f x = g x. *)
(* Abort. *)

(* Implement wqd : forall (A : Type) (B : A -> Prop), forall x, B x. *)
(* Abort. *)

(* Implement foo : forall (A : Type) (a : A) (p : a = a), p = eq_refl a. *)
(* Abort. *)


(* Is is necessary to import Template.trad for the definition of prod' *)
Require Import Template.Translation Template.trad.

(* Test Quote Type. *)
(* Set Printing Universes. *)
(* Make Definition t := (Ast.tSort (Ast.sType BinNums.xH)). *)
(* Print t. *)
(* Print Universes. *)

Let T := Type.
Check (T : T).

Implement t' : Set.
cbn. exists nat. exact (fun _ => bool).
Defined.

Definition t := Set.
Translate t.

Implement y : Type.
refine (@mk_sig Type (fun A : Type => A -> Type) Type _).
auto.
Defined.

Implement yy : Type -> Type.
cbn. unshelve econstructor.
Abort.

Translate unit.
exact (mk_sig unit (fun _ => unit)).
Defined.
Print unitᵗ.

Set Printing Universes.
Translate sigma.
cbn.
refine (@mk_sig _ _ _ _).
econstructor.

Translate eq.

Definition equiv A B :=
  sigma (A -> B)
        (fun f => sigma (B -> A)
                     (fun g => forall x, g (f x) = x)).

Translate equiv.

Implement notUnivalence : exists 

Translate sigma.
Translate pair.
(* Translate fst'. *)
(* Translate snd'. *)
Translate bool.
Translate true.
Translate false.

Definition n : (fun x => x) Type := nat.

Definition g := prod Prop Type.
Definition f := g.

Axiom tr : nat.

(* Fail Translate tr. *)
Translate g.
Translate f.
Print fᵗ.

Implement t2 : bool as totot.
econstructor.
Defined.
Print t2.
Print totot.

Definition t4 := (t2, true).
Translate t4.

Implement t3 : t2 = t2.
econstructor.
Defined.

Definition t3' := pair' _ _ t3 nat.
Translate t3'.
Print t3'ᵗ.

Implement nnnn : (nat -> nat).
(* Implement nnnn : prod' (nat -> nat) bool. *)
econstructor; econstructor.
Defined.

Set Printing Universes.

Definition t5 := forall X:Set, X.
(* Print Sorted Universes. *)
Translate t5.
Print Sorted Universes.

(* Axiom a : forall X, X. *)

Implement y : forall X:Set, X.
(* Print Sorted Universes. *)
refine (pair' _ _ _ _).
admit. econstructor.
Admitted.

Translate nat.
Translate unit.

Definition t := (fun x : nat => x).
Translate t. 

(* Set Primitive Projections. *)
(* Record prod' (A B : Set) : Set := *)
(*   pair' { fst' : A ; snd' : B }. *)
(* Arguments fst' {A B} _. *)
(* Arguments snd' {A B} _. *)

(* Translate prod'. *)
Definition mm := (pair' _ _ true tt).(fst').
Translate mm.
Eval compute in mmᵗ.

(* Require Import BoolProd. *)

(* Declare ML Module "mTranslate". *)
(* Open Scope my_scope. *)


Tactic Notation "intro'" ident(X) := econstructor; [intro X|exact true].
Tactic Notation "intros'" := repeat (refine (_, true); intro).
Tactic Notation "specialize'" hyp(H) uconstr(t) := apply fst' in H; specialize (H t).

Translate False.
Translate eq.

(* This translation allow to implement the negation of funext. *)
(* Test Quote  *)
Implement notFunext :
  ((forall (A B : Set) (f g : A -> B), (forall x:A, f x = f x) -> f = g) -> False).
Proof.
  intro' H.
  specialize' H unit.
  specialize' H unit.
  specialize' H (pair' _ _ (fun x => x) true).
  specialize' H (pair' _ _ (fun x => x) false). cbn in *.
  specialize' H (pair' _ _ (fun x => eq_refl) true).
  apply (f_equal snd') in H; cbn in H.
  discriminate H.
Defined.

(* (* A more constructive version on inhabited types. *) *)
(* Implement notFunext' : forall (A B : Type), *)
(*     B -> {f : A -> B & { g : A -> B & ((forall x, f x = g x) -> f = g) -> False}}. *)
(* Proof. *)
(*   intro' A. intro' B. intro' y. *)
(*   pose (f := fun _ : A => y). exists (f, true). exists (f, false). *)
(*   intro' H. *)
(*   specialize' H (fun x => eq_refl, true). *)
(*   apply (f_equal snd) in H; cbn in H. *)
(*   discriminate H. *)
(* Defined. *)


(* Check notFunext'. *)
(* Compute notFunext'ᶠ. *)


(* Definition notFunext'Nat := notFunext' nat nat. *)

(* (* If we want to prove some result about notFunext'Nat we first hae to extend the translation to it. *) *)
(* Translate notFunext'Nat. *)

(* (* Now we can postulate new principles about notFunext'Nat, always preserving consistency. *) *)
(* Implement notFunext'Nat01 : notFunext'Nat 0 = notFunext'Nat 1 -> False. *)
(* Proof. *)
(*   compute. refine (_, true). intro H. *)
(*   pose proof (f_equal (@projT1 _ _) H); cbn in *. *)
(*   apply (f_equal fst) in H0; cbn in *. *)
(*   assert ((fun _ : nat => 0) 0 = (fun _ : nat => 1) 0). *)
(*   change ((fun _ : nat => 0) 0 = (fun _ : nat => 1) 0). rewrite H0. reflexivity. *)
(*   discriminate H1. *)
(* Defined. *)



(* ** Some check of the translation on other types. *** *)

Implement f : forall (f : Type -> Type), f Type.
Abort.

Implement foo : forall A B : Type, forall (f g : A -> B), forall x, f x = g x.
Abort.

Implement wqd : forall (A : Type) (B : A -> Prop), forall x, B x.
Abort.

Implement foo : forall (A : Type) (a : A) (p : a = a), p = eq_refl a.
Abort.