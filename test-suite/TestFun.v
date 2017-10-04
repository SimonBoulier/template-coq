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


Open Scope sigma_scope.

Implement t' : Set.
cbn. exists nat. exact (fun _ => bool).
Defined.

Definition t := Set.
Translate t.
Fail Implement Existing t.
Print Visibility.

Implement y : Type.
refine (@mk_sig Type (fun A : Type => A -> Type) Type _).
auto.
Defined.

Fail Translate unit.
Implement Existing unit.
exact (mk_sig unit (fun _ => unit)).
Defined.
Print unitᵗ.

Implement Existing tt.
unshelve econstructor. exact tt. exact tt.
Defined.

Fail Translate tt.

Implement ttt : unit.
cbn.
econstructor.
exact tt. exact tt.
Defined.
Print tttᵗ.

Axiom tr : unit.
Fail Translate tr.
Implement Existing tr.
Admitted.


Notation "'TYPE'" := (exists A, A -> Type).
Notation "'El' A" := (sigma (π1 A) (π2 A)) (at level 20).

Definition Type_cst := Type.
Translate Type_cst as Typeᶠ.

(* Definition Typeᶠ : El Typeᶠ := *)
(*   @mk_sig Type (fun A => A -> Type) Type (fun A => A -> Type). *)

Check Typeᶠ : El Typeᶠ.

Definition mkTYPE (A₀ : Type) (Aᴿ : A₀ -> Type) : El Typeᶠ :=
  @mk_sig Type (fun A₀ => A₀ -> Type) A₀ Aᴿ.

Definition Prodᶠ (A : El Typeᶠ) (B : El A -> El Typeᶠ) : El Typeᶠ :=
  mkTYPE
    (forall x : El A, (B x).1)
    (fun f₀ => forall x : El A, (B x).2 (f₀ x)).

Notation "A →ᶠ B" := (Prodᶠ A (fun _ => B)) (at level 99, right associativity, B at level 200).
Notation "'Πᶠ'  x .. y , P" := (Prodᶠ _ (fun x => .. (Prodᶠ _ (fun y => P)) ..))
  (at level 200, x binder, y binder, right associativity).

Definition Lamᶠ {A : El Typeᶠ} {B : El A -> El Typeᶠ} (f : forall x : El A, El (B x)) : El (Prodᶠ A B).
Proof.
unshelve refine (_ ; _).
+ refine (fun x => (f x).1).
+ refine (fun x => (f x).2).
Defined.

Notation "'λᶠ'  x .. y , t" := (Lamᶠ (fun x => .. (Lamᶠ (fun y => t)) ..))
  (at level 200, x binder, y binder, right associativity).

Definition Appᶠ {A B} (f : El (Prodᶠ A B)) (x : El A) : El (B x).
Proof.
unshelve refine (_ ; _).
+ refine (f.1 x).
+ refine (f.2 x).
Defined.

Notation "t · u" := (Appᶠ t u) (at level 65, left associativity).


Definition sigmaᵀ (A : El Typeᶠ) (P : El (A →ᶠ Typeᶠ)) : Type :=
  sigma (El A) (fun x => El (P · x)).

Definition existᵀ (A : El Typeᶠ) (P : El (A →ᶠ Typeᶠ))
           (x : El A) (y : El (P · x)) : sigmaᵀ A P
  := mk_sig x y.

Inductive sigmaᴿ (A : El Typeᶠ) (P : El (A →ᶠ Typeᶠ)) : sigmaᵀ A P -> Type :=
| existᴿ : forall (x : El A) (y : El (P · x)), sigmaᴿ A P (existᵀ A P x y).

Definition sigmaᶠ : El (Πᶠ (A : El Typeᶠ) (P : El (A →ᶠ Typeᶠ)), Typeᶠ).
Proof.
refine (λᶠ A P, _).
unshelve refine (mkTYPE _ (sigmaᴿ A P)).
Defined.

Definition existᶠ : El (Πᶠ (A : El Typeᶠ) (P : El (A →ᶠ Typeᶠ)) (x : El A) (y : El (P · x)),
  sigmaᶠ · A · P).
Proof.
refine (λᶠ A P x y, _).
refine (mk_sig (existᵀ A P x y) (existᴿ A P x y)).
Defined.


Implement Existing sigma.
exact sigmaᶠ.
Defined.

Implement Existing mk_sig.
exact existᶠ.
Defined.


Inductive eq2 (A : El Typeᶠ) (x : El A) :
  forall (y : El A), eq (π1 x) (π1 y) -> Prop :=
| refl2 : eq2 A x x eq_refl.


Definition eqᶠ : El (Πᶠ (A : El Typeᶠ), A →ᶠ A →ᶠ Typeᶠ).
Proof.
refine (λᶠ A x y, _).
unshelve refine (mkTYPE _ _).
+ refine (eq x.1 y.1).
+ refine (eq2 A x y).
Defined.

Implement Existing eq.
unshelve econstructor.
exact (fun A x y => π1 x = π1 y).
exact eq2.
Defined.


Definition reflᶠ : El (Πᶠ (A : El Typeᶠ) (x : El A), eqᶠ · A · x · x).
Proof.
refine (λᶠ A x, _).
unshelve refine (_; refl2 A x).
Defined.



Notation " A × B " := (sigma A (fun _ => B)) (at level 30) : type_scope.


Definition equiv (A B : Type) :=
  exists (f : A -> B) (g : B -> A), (forall x, g (f x) = x) × (forall y, f (g y) = y).
Translate equiv.

Implement Existing False.
exact (False; fun _ => False).
Defined.

Definition not A := A -> False.
Translate not.

(* Definition hasTwoElements A *)
(*   := exists x y, @eq A x y -> False. *)
(* Translate hasTwoElements. *)

Definition HasTwoElFstComponentᶠ : El (Typeᶠ →ᶠ Typeᶠ) :=
  λᶠ (T : El Typeᶠ), mkTYPE (exists (x y : T.1), x = y -> False) (fun _ => unit).

Implement notUnivalence :
  exists A B, (equiv A B) × exists P, P A × not (P B).
Proof.
simple refine (existᶠ · _ · _ · _ · _).
exact (bool:Type; fun _=> unit:Type).
simple refine (existᶠ · _ · _ · _ · _).
exact (unit:Type; fun _ => bool:Type).
simple refine (existᶠ · _ · _ · _ · _).
- simple refine (existᶠ · _ · _ · _ · _).
  exists π2. exact π1.
  simple refine (existᶠ · _ · _ · _ · _).
  exists π2. exact π1.
  simple refine (existᶠ · _ · _ · _ · _);
    cbn; unshelve econstructor; reflexivity.
- simple refine (existᶠ · _ · _ · _ · _).
  exact HasTwoElFstComponentᶠ.
  simple refine (existᶠ · _ · _ · _ · _).
  + cbn. refine (_; tt). exists true. exists false.
    discriminate 1.
  + refine (λᶠ p, _). cbn in p.
    destruct p as [p _].
    destruct p as [[] [[] p]].
    contradiction p. reflexivity.
Defined.





  
(* ** Some check of the translation on other types. *** *)

Implement f : forall (f : Type -> Type), f Type.
Abort.

Implement foo : forall A B : Type, forall (f g : A -> B), forall x, f x = g x.
Abort.

Implement wqd : forall (A : Type) (B : A -> Prop), forall x, B x.
Abort.

(* Implement foo : forall (A : Type) (a : A) (p : a = a), p = eq_refl a. *)
(* Abort. *)