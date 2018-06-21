(* -*- coq-prog-args: ("-type-in-type" "-top" "Translations.tsl_param3") -*-  *)
Require Import Template.All.
From Translations Require Import translation_utils.
Import String Lists.List.ListNotations MonadNotation.
Open Scope list_scope. Open Scope string_scope.

(* Local Existing Instance config.default_checker_flags. *)
Require Import MiniHoTT_paths.

Reserved Notation "'tsl_ty_param'".


Quote Definition tSigma := @sigT.
Quote Definition tPair := @existT.
Definition pair (typ1 typ2 t1 t2 : term) : term
  := tApp tPair [ typ1 ; typ2 ; t1 ; t2].
Definition pack (t u : term) : term
  := tApp tSigma [ t ; u ].
Definition sigma_ind := Eval compute in match tSigma with tInd i _ => i | _ =>  mkInd "bug: sigma not an inductive"%string 0 end.
Definition proj1 (t : term) : term
  := tProj (sigma_ind, 2, 0) t.
Definition proj2 (t : term) : term
  := tProj (sigma_ind, 2, S 0) t.
Definition proj (b : bool) (t : term) : term
  := tProj (sigma_ind, 2, if b then 0 else S 0) t.


Fixpoint refresh_universes (t : term) {struct t} :=
  match t with
  | tSort s => tSort (if Universe.is_level s then s else [])
  | tProd na b t => tProd na b (refresh_universes t)
  | tLetIn na b t' t => tLetIn na b t' (refresh_universes t)
  | _ => t
  end.

Local Instance tit : checker_flags
  := {| check_univs := false |}.

(* if b it is the first translation, else the second *)
Fixpoint tsl_rec (fuel : nat) (Σ : global_context) (E : tsl_table) (Γ : context) (b : bool) (t : term) {struct fuel}
  : tsl_result term :=
  match fuel with
  | O => raise NotEnoughFuel
  | S fuel =>
  match t with
  | tRel n => ret (proj b (tRel n))
  | tSort s => if b then ret (tSort s)
              else ret (tLambda (nNamed "A") (tSort s) (tProd nAnon (tRel 0) (tSort s)))
  | tCast t c A => if b then
                    t1 <- tsl_rec fuel Σ E Γ true t ;;
                    A1 <- tsl_rec fuel Σ E Γ true A ;;
                    ret (tCast t1 c A1)
                  else
                    t1 <- tsl_rec fuel Σ E Γ true t ;;
                    t2 <- tsl_rec fuel Σ E Γ false t ;;
                    A2 <- tsl_rec fuel Σ E Γ false A ;;
                    ret (tCast t2 c (tApp A2 [t1]))
  | tProd n A B => if b then
                    A' <- tsl_ty_param fuel Σ E Γ A ;;
                    B1 <- tsl_rec fuel Σ E (Γ ,, vass n A) true B ;;
                    ret (tProd n A' B1)
                  else
                    A' <- tsl_ty_param fuel Σ E Γ A ;;
                    B1 <- tsl_rec fuel Σ E (Γ ,, vass n A) true B ;;
                    B2 <- tsl_rec fuel Σ E (Γ ,, vass n A) false B ;;
                    ret (tLambda (nNamed "f") (tProd n A' B1)
                                 (tProd n (lift 1 0 A')
                                        (tApp (lift 1 1 B2)
                                              [tApp (tRel 1) [tRel 0]])))
  | tLambda n A t => A' <- tsl_ty_param fuel Σ E Γ A ;;
                    t' <- tsl_rec fuel Σ E (Γ ,, vass n A) b t ;;
                    ret (tLambda n A' t')
  | tLetIn n t A u => t' <- tsl_term fuel Σ E Γ t ;;
                     A' <- tsl_ty_param fuel Σ E Γ A ;;
                     u' <- tsl_rec fuel Σ E (Γ ,, vdef n t A) b u ;;
                     ret (tLetIn n t' A' u')
  | tApp t u => t' <- tsl_rec fuel Σ E Γ b t ;;
               u' <- monad_map (tsl_term fuel Σ E Γ) u ;;
               ret (tApp t' u')
  | tConst _ _ as t
  | tInd _ _ as t
  | tConstruct _ _ _ as t => t' <- tsl_term fuel Σ E Γ t ;;
                            ret (proj b t')
  | _ => raise TranslationNotHandeled
  end
  end
with tsl_term  (fuel : nat) (Σ : global_context) (E : tsl_table) (Γ : context) (t : term) {struct fuel}
  : tsl_result term :=
  match fuel with
  | O => raise NotEnoughFuel
  | S fuel =>
  match t with
  | tRel n => ret (tRel n)
  | tSort s => ret (pair (tSort []) (tLambda (nNamed "A") (tSort []) (tProd nAnon (tRel 0) (tSort []))) (tSort s) (tLambda (nNamed "A") (tSort s) (tProd nAnon (tRel 0) (tSort s))))
  | tCast t c A => t' <- tsl_term fuel Σ E Γ t ;;
                  A' <- tsl_ty_param fuel Σ E Γ A ;;
                  ret (tCast t' c A')
  | tConst s univs =>
    match lookup_tsl_table E (ConstRef s) with
    | Some t => ret t
    | None => raise (TranslationNotFound s)
    end
  | tInd i univs =>
    match lookup_tsl_table E (IndRef i) with
    | Some t => ret t
    | None => raise (TranslationNotFound (string_of_gref (IndRef i)))
    end
  | tConstruct i n univs =>
    match lookup_tsl_table E (ConstructRef i n) with
    | Some t => ret t
    | None => raise (TranslationNotFound (string_of_gref (ConstructRef i n)))
    end
  | t => match infer Σ Γ t with
         | Checked typ => let typ := refresh_universes typ in
                         t1 <- tsl_rec fuel Σ E Γ true t ;;
                         t2 <- tsl_rec fuel Σ E Γ false t ;;
                         typ1 <- tsl_rec fuel Σ E Γ true typ ;;
                         typ2 <- tsl_rec fuel Σ E Γ false typ ;;
                         ret (pair typ1 typ2 t1 t2)
        | TypeError t => raise (TypingError t)
        end
  end
  end
where "'tsl_ty_param'" := (fun fuel Σ E Γ t =>
                        t1 <- tsl_rec fuel Σ E Γ true t ;;
                        t2 <- tsl_rec fuel Σ E Γ false t ;;
                        ret (pack t1 t2)).



Instance tsl_param : Translation
  := {| tsl_id := tsl_ident ;
        tsl_tm := fun ΣE => tsl_term fuel (fst ΣE) (snd ΣE) [] ;
        tsl_ty := fun ΣE => tsl_ty_param fuel (fst ΣE) (snd ΣE) [] ;
        tsl_ind := todo |}.



Notation "'TYPE'" := (exists A, A -> Type).
Notation "'El' A" := (@sigT A.1 A.2) (at level 20).

Run TemplateProgram (TC <- tImplement emptyTC "toto" (forall X, X) ;;
                     tmPrint TC).
Next Obligation.
Abort.


Definition Ty := Type.
(* Set Printing Universes. *)
Run TemplateProgram (tTranslate emptyTC "Ty").
Check Tyᵗ : El Tyᵗ.

(* Definition mk_sig : forall {A} {B : A -> Type} (π1 : A), B π1 -> sigma A B *)
(*   := @mk_sig. *)
(* Axiom sigma_rect : forall A (B : A -> Type) (P : sigma A B -> Type), *)
(*     (forall (x : A) (y : B x), P (mk_sig x y)) -> forall s, P s. *)
(*   (* intros A B P X s. apply X. Defined. *) *)



Run TemplateProgram (TC <- tImplementExisting emptyTC "sigT" ;;
                     tmDefinition "TC" TC).
Next Obligation.
  unshelve econstructor.
(*   - intros A B. refine (sigma (El A) (fun x => sigma (B.1 x) (B.2 x))). *)
(*   - cbn. intros A B X. exact unit.  *)
(* Defined. *)
  - intros A B. refine (@sigT (El A) B.1).
  - cbn; intros A B. refine (fun x => B.2 x.1 x.2).
Defined.

Run TemplateProgram (TC <- tImplementExisting TC "existT" ;;
                     tmDefinition "TC'" TC).
Next Obligation.
  unshelve econstructor.
(*   - intros A B x y. econstructor. exact y. *)
(*   - intros A B π1 H. constructor.  *)
(* Defined. *)
  - intros A B x y. econstructor. exact y.1.
  - cbn; intros A B x y. exact y.2.
Defined.

(* Compute TC'.  *)
Time Run TemplateProgram (TC <- tImplementExisting TC' "sigT_ind" ;;
                          tmDefinition "TC''" TC).
Check "yo".
Next Obligation.
  unshelve econstructor.
(*   - intros A B P [X1 X2] [s []]. apply X1. *)
(*   - intros A B P [X1 X2] [s []]. apply X2. *)
(* Defined. *)
  - intros A B P [X1 X2] [s s']. apply (X1 s.1 (s.2; s')).
  - intros A B P [X1 X2] [s s']. apply (X2 s.1 (s.2; s')).
Defined.


Run TemplateProgram (TC <- tImplementExisting TC'' "paths" ;;
                     tmDefinition "TC3" TC).
Next Obligation.
  unshelve econstructor.
  - intros A x y. refine (x.1 = y.1).
  - cbn; intros A x y p. refine (p # x.2 = y.2).
Defined.


Run TemplateProgram (TC <- tImplementExisting TC3 "idpath" ;;
                     tmDefinition "TC4" TC).
Next Obligation.
  unshelve econstructor; reflexivity.
Defined.

Run TemplateProgram (TC <- tImplementExisting TC4 "paths_ind" ;;
                     tmDefinition "TC5" TC).
Next Obligation.
  unshelve econstructor.
  - intros A [x x'] P X [y y'] [p q]. cbn in *. destruct p, q; cbn.
    exact X.1.
  - intros A [x x'] P X [y y'] [p q]. cbn in *. destruct p, q; cbn.
    exact X.2.
Defined.


Definition Funext := forall A (B : A -> Type) (f g : forall x, B x), (forall x, paths (f x) (g x)) -> paths f g.

Run TemplateProgram (tTranslate TC5 "Funext").

Goal Funext -> El Funextᵗ.
  simpl. intro H. unshelve econstructor.
  - intros A B f g X. apply H. exact X.1.
  - intros A B f g [X1 X2]; cbn in *.
    apply H. intro x. rewrite transport_forall_constant.
    specialize (X2 x).
    refine (_ @ X2).
    rewrite transport_compose.
    eapply ap10. eapply ap.
    rewrite ap_apply_lD.
Admitted.


Definition FALSE := forall X, X.
Run TemplateProgram (tTranslate emptyTC "FALSE").

Proposition consistency_preservation : El FALSEᵗ -> FALSE.
  compute.
  intros [f _] X.
  exact (f (X; fun _ => unit)).
Defined.


Definition UIP := forall A (x y : A) (p q : paths x y), paths p q.

Run TemplateProgram (tTranslate TC5 "UIP").

Proposition uip_preservation : UIP -> El UIPᵗ.
  simpl. intro H. unshelve econstructor.
  - intros A x y p q. apply H.
  - cbn. intros A x y p q.  apply H.
Defined.

Notation " A × B " := (@sigT A (fun _ => B)) (at level 30) : type_scope.

Definition equiv (A B : Type) : Type :=
  (* Type. *)
  exists (f : A -> B) (g : B -> A),
    (forall x, paths (g (f x)) x) × (forall x, paths (f (g x)) x).

Run TemplateProgram (TC <- tImplementExisting TC5 "False" ;;
                     tmDefinition "TC6" TC).
Next Obligation.
  unshelve econstructor.
  - exact False.
  - intros _. exact False.
Defined.




Check "go".
Run TemplateProgram (
                       ΣE <- tTranslate TC6 "equiv" ;;
                       tmPrint "lo" ;;
                       H <- tImplement ΣE "notUnivalence"
                       (exists A B : Set, (equiv A B) × exists P, P A × ((P B) -> False)) ;;
                       tmPrint "done"
                     ).
Check "proof".
Next Obligation.
Set Printing Universes. compute. unshelve econstructor. exists (bool:Type; fun _=> unit:Type).

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
  exact HasTwoElFstComponentᵗ.
  simple refine (existᶠ · _ · _ · _ · _).
  + cbn. refine (_; tt). exists true. exists false.
    discriminate 1.
  + compute.
    split; (intro p;
            destruct p as [p _];
            destruct p as [[] [[] p]];
            contradiction p; reflexivity).
Defined.

Check "ok!".












Definition mkTYPE (A₀ : Type) (Aᴿ : A₀ -> Type) : El Tyᵗ :=
  @mk_sig Type (fun A₀ => A₀ -> Type) A₀ Aᴿ.

Definition Prodᶠ (A : El Tyᵗ) (B : El A -> El Tyᵗ) : El Tyᵗ :=
  mkTYPE
    (forall x : El A, (B x).1)
    (fun f₀ => forall x : El A, (B x).2 (f₀ x)).

Notation "A →ᶠ B" := (Prodᶠ A (fun _ => B)) (at level 99, right associativity, B at level 200).
Notation "'Πᶠ'  x .. y , P" := (Prodᶠ _ (fun x => .. (Prodᶠ _ (fun y => P)) ..))
  (at level 200, x binder, y binder, right associativity).

Definition Lamᶠ {A : El Tyᵗ} {B : El A -> El Tyᵗ} (f : forall x : El A, El (B x)) : El (Prodᶠ A B).
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

Notation "t · u" := (Appᶠ t u) (at level 64, left associativity).


Definition sigmaᵀ (A : El Tyᵗ) (P : El (A →ᶠ Tyᵗ)) :=
  sigma (El A) (fun x => El (P · x)).

Eval compute in sigmaᵀ.
Definition existᵀ (A : El Tyᵗ) (P : El (A →ᶠ Tyᵗ))
           (x : El A) (y : El (P · x)) : sigmaᵀ A P
  := mk_sig x y.

Inductive sigmaᴿ (A : El Tyᵗ) (P : El (A →ᶠ Tyᵗ)) : sigmaᵀ A P -> Type :=
| existᴿ : forall (x : El A) (y : El (P · x)), sigmaᴿ A P (existᵀ A P x y).

Goal forall (A : El Tyᵗ) (P : El (A →ᶠ Tyᵗ)) x, sigmaᴿ A P x.
destruct x; constructor .
Defined.

Definition sigmaᶠ : El (Πᶠ (A : El Tyᵗ) (P : El (A →ᶠ Tyᵗ)), Tyᵗ).
Proof.
refine (λᶠ A P, _).
unshelve refine (mkTYPE _ (sigmaᴿ A P)).
Defined.

Definition existᶠ : El (Πᶠ (A : El Tyᵗ) (P : El (A →ᶠ Tyᵗ)) (x : El A) (y : El (P · x)),
  sigmaᶠ · A · P).
Proof.
refine (λᶠ A P x y, _).
refine (mk_sig (existᵀ A P x y) (existᴿ A P x y)).
Defined.


Inductive paths2 (A : El Tyᵗ) (x : El A) :
  forall (y : El A), (π1 x) = (π1 y) -> Type :=
| refl2 : paths2 A x x 1.


Definition pathsᶠ : El (Πᶠ (A : El Tyᵗ), A →ᶠ A →ᶠ Tyᵗ).
Proof.
refine (λᶠ A x y, _).
unshelve refine (mkTYPE _ _).
+ refine (paths x.1 y.1).
+ refine (paths2 A x y).
Defined.

Definition reflᶠ : El (Πᶠ (A : El Tyᵗ) (x : El A), pathsᶠ · A · x · x).
Proof.
refine (λᶠ A x, _).
unshelve refine (_; refl2 A x).
Defined.

Definition Falseᶠ : El Tyᵗ.
  exists False. exact (fun _ => False).
Defined.
  

Quote Recursively Definition sigma_prog := @sigma.
Quote Recursively Definition paths_prog := @paths.
Quote Recursively Definition false_prog := @False.
Definition sigma_decl := Eval compute in
      lookup_mind_decl "Translations.sigma.sigma" (fst sigma_prog).
Definition paths_decl := Eval compute in
      lookup_mind_decl "Translations.MiniHoTT_paths.paths" (fst paths_prog).
Definition false_decl := Eval compute in
      lookup_mind_decl "Coq.Init.Logic.False" (fst false_prog).


Definition ΣE : option tsl_context :=
  sd <- sigma_decl ;;
  ed <- paths_decl ;;
  fd <- false_decl ;;
  let Σ' := [InductiveDecl "Coq.Init.Logic.False" fd;
            InductiveDecl "Translations.MiniHoTT_paths.paths" ed;
            InductiveDecl "Translations.sigma.sigma" sd] in
  let Σ' := reconstruct_global_context Σ' in
  let E' := [(IndRef (mkInd "Translations.sigma.sigma" 0),
              tConst "sigmaᶠ" []);
             (ConstructRef (mkInd "Translations.sigma.sigma" 0) 0,
              tConst "existᶠ" []);
             (IndRef (mkInd "Translations.MiniHoTT_paths.paths" 0), tConst "pathsᶠ" []);
             (IndRef (mkInd "Coq.Init.Logic.False" 0), tConst "Falseᶠ" [])
            ] in
  ret (Σ', E').

Definition HasTwoElFstComponentᵗ : El (Tyᵗ →ᶠ Tyᵗ)
  := λᶠ (T : El Tyᵗ), mkTYPE (exists (x y : T.1), x = y -> False) (fun _ => unit).


