Require Import Template.Template Template.Ast Template.sigma.
Require Import Template.Induction Template.LiftSubst Template.Typing Template.Checker.
Require Import Arith.Compare_dec.
Require Import  Template.translation_utils.
Import String Lists.List.ListNotations MonadNotation.
Open Scope list_scope. Open Scope string_scope.


Reserved Notation "'tsl_ty'".


Fixpoint tsl_rec1 (n : nat) (t : term) {struct t} : term :=
  match t with
  | tRel k => if ge_dec k n then proj1 t else t
  (* | tMeta : nat -> term *)
  (* | tEvar : nat -> list term -> term *)
  | tCast t c a => tCast (tsl_rec1 n t) c (tsl_rec1 n a)
  | tProd x A B => tProd x (tsl_rec1 n A) (tsl_rec1 (n+1) B)
  | tLambda x A t => tLambda x (tsl_rec1 n A) (tsl_rec1 (n+1) t)
  | tLetIn x a t u => tLetIn x (tsl_rec1 n a) (tsl_rec1 n t) (tsl_rec1 (n+1) u)
  | tApp t lu => tApp (tsl_rec1 n t) (List.map (tsl_rec1 n) lu)
  (* | tCase : inductive * nat -> term -> term -> list (nat * term) -> term *)
  | tProj p t => tProj p (tsl_rec1 n t)
  (* | tFix : mfixpoint term -> nat -> term *)
  (* | tCoFix : mfixpoint term -> nat -> term *)
  | _ => t
  end.
    

Fixpoint tsl_rec2 (fuel : nat) (Σ : global_context) (E : tsl_context) (Γ : context) (t : term) {struct fuel}
  : tsl_result term :=
  match fuel with
  | O => raise NotEnoughFuel
  | S fuel =>
  match t with
  | tRel n => ret (proj2 (tRel n))
  | tSort s => ret (tLambda (nNamed "A") (tSort s)
                           (tProd nAnon (tRel 0) (tSort s)))
  | tCast t c A => let t1 := tsl_rec1 0 t in
                  t2 <- tsl_rec2 fuel Σ E Γ t ;;
                  A2 <- tsl_rec2 fuel Σ E Γ A ;;
                  ret (tCast t2 c (tApp A2 [t1]))
  | tProd n A B => let ΠAB' := tsl_rec1 0 (tProd n A B) in
                  let B1 := tsl_rec1 0 B in
                  A' <- tsl_ty fuel Σ E Γ A ;;
                  B2 <- tsl_rec2 fuel Σ E (Γ ,, vass n A) B ;;
                  ret (tLambda (nNamed "f") ΠAB'
                               (tProd n (lift 1 0 A')
                                      (tApp (lift 1 1 B2)
                                            [tApp (tRel 1) [proj1 (tRel 0)]])))
  | tLambda n A t => A' <- tsl_ty fuel Σ E Γ A ;;
                    t' <- tsl_rec2 fuel Σ E (Γ ,, vass n A) t ;;
                    ret (tLambda n A' t')
  | tLetIn n t A u => t' <- tsl_term fuel Σ E Γ t ;;
                     A' <- tsl_ty fuel Σ E Γ A ;;
                     u' <- tsl_rec2 fuel Σ E (Γ ,, vdef n t A) u ;;
                     ret (tLetIn n t' A' u')
  | tApp t u => t' <- tsl_rec2 fuel Σ E Γ t ;;
               u' <- monad_map (tsl_term fuel Σ E Γ) u ;;
               ret (tApp t' u')
  | tConst _ as t
  | tInd _ as t
  | tConstruct _ _ as t => t' <- tsl_term fuel Σ E Γ t ;;
                          ret (proj2 t')
  | _ => raise TranslationNotHandeled
  end
  end
with tsl_term  (fuel : nat) (Σ : global_context) (E : tsl_context) (Γ : context) (t : term) {struct fuel}
  : tsl_result term :=
  match fuel with
  | O => raise NotEnoughFuel
  | S fuel =>
  match t with
  | tRel n => ret (tRel n)
  | tCast t c A => t' <- tsl_term fuel Σ E Γ t ;;
                  A' <- tsl_ty fuel Σ E Γ A ;;
                  ret (tCast t' c A')
  | tConst s => match lookup_tsl_ctx E (ConstRef s) with
               | Some t => ret t
               | None => raise (TranslationNotFound s)
               end
  | tInd i =>
    match lookup_tsl_ctx E (IndRef i) with
    | Some t => ret t
    | None => raise (TranslationNotFound (string_of_gref (IndRef i)))
    end
  | tConstruct i n =>
    match lookup_tsl_ctx E (ConstructRef i n) with
    | Some decl => raise TranslationNotHandeled
    | None => raise (TranslationNotFound (string_of_gref (ConstructRef i n)))
    end
  | t => match infer Σ Γ t with
        | Checked typ => let t1 := tsl_rec1 0 t in
                        t2 <- tsl_rec2 fuel Σ E Γ t ;;
                        let typ1 := tsl_rec1 0 typ in
                        typ2 <- tsl_rec2 fuel Σ E Γ typ ;;
                        ret (pair typ1 typ2 t1 t2)
        | TypeError t => raise (TypingError t)
        end
  end
  end
where "'tsl_ty'" := (fun fuel Σ E Γ t =>
                        let t1 := tsl_rec1 0 t in
                        t2 <- tsl_rec2 fuel Σ E Γ t ;;
                        ret (pack t1 t2)).


Instance tsl_param_instance_term : Translation
  := {| tsl_tm := fun Σ E => tsl_term fuel Σ E [] |}.

Instance tsl_param_instance_type : TranslationType
  := {| tsl_typ := fun Σ E => tsl_ty fuel Σ E [] |}.

Declare ML Module "translation_plugin".


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
Definition s := sigma.
Translate s.
Implement notUnivalence : 
  exists A B : Type, (equiv A B) × exists P, P A × not (P B).
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


Definition FALSE := forall X, X.
Translate FALSE.

Proposition consistency_preservation : El FALSEᵗ -> FALSE.
  compute.
  intros [f _] X.
  exact (f (X; fun _ => unit)).
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