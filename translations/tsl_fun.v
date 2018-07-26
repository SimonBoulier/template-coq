(* -*- coq-prog-args: ("-type-in-type" "-top" "Translations.tsl_fun") -*-  *)
Require Import Template.All.
From Translations Require Import translation_utils.
Import String Lists.List.ListNotations MonadNotation.
Open Scope list_scope. Open Scope string_scope.

Local Existing Instance config.default_checker_flags.

Set Primitive Projections.
Record prod A B := pair { π1 : A ; π2 : B }.

Arguments π1 {_ _} _.
Arguments π2 {_ _} _.
Arguments pair {_ _} _ _.

Notation "( x ; y )" := (pair x y) : prod_scope.
Notation " A × B " := (prod A B) (at level 30) : type_scope.

Quote Definition tprod := prod.
Quote Definition tpair := @pair.
Definition prod_ind := Eval compute in
  match tprod with tInd i _ => i | _ => mkInd "bug: prod not an inductive" 0 end.
Definition proj1 (t : term) : term
  := tProj (prod_ind, 2, 0) t.
Definition proj2 (t : term) : term
  := tProj (prod_ind, 2, 1) t.

Quote Definition tbool := bool.
Quote Definition ttrue := true.
Definition timesBool (A : term) := tApp tprod [A; tbool].
Definition pairTrue typ tm := tApp tpair [typ; tbool; tm; ttrue].




Local Instance tit : checker_flags
  := {| check_univs := false |}.

Fixpoint tsl_rec (fuel : nat) (Σ : global_context) (E : tsl_table) (Γ : context) (t : term) {struct fuel}
  : tsl_result term :=
  match fuel with
  | O => raise NotEnoughFuel
  | S fuel =>
  match t with
  | tRel  n => ret (tRel n)
  | tSort s => ret (tSort s)

  | tCast t c A => t' <- tsl_rec fuel Σ E Γ t ;;
                  A' <- tsl_rec fuel Σ E Γ A ;;
                  ret (tCast t' c A')

  | tProd n A B => A' <- tsl_rec fuel Σ E Γ A ;;
                  B' <- tsl_rec fuel Σ E (Γ ,, vass n A) B ;;
                  ret (timesBool (tProd n A' B'))

  | tLambda n A t => A' <- tsl_rec fuel Σ E Γ A ;;
                    t' <- tsl_rec fuel Σ E (Γ ,, vass n A) t ;;
                    match infer Σ (Γ ,, vass n A) t with
                    | Checked B =>
                      B' <- tsl_rec fuel Σ E (Γ ,, vass n A) B ;;
                      ret (pairTrue (tProd n A' B') (tLambda n A' t'))
                    | TypeError t => raise (TypingError t)
                    end

  | tLetIn n t A u => t' <- tsl_rec fuel Σ E Γ t ;;
                     A' <- tsl_rec fuel Σ E Γ A ;;
                     u' <- tsl_rec fuel Σ E (Γ ,, vdef n t A) u ;;
                     ret (tLetIn n t' A' u')

  | tApp t us => t' <- tsl_rec fuel Σ E Γ t ;;
                monad_fold_left (fun t u => u' <- tsl_rec fuel Σ E Γ u ;;
                                         ret (tApp (proj1 t) [u'])) us t'

  | tConst s univs => lookup_tsl_table' E (ConstRef s)
  | tInd i univs => lookup_tsl_table' E (IndRef i)
  | tConstruct i n univs => lookup_tsl_table' E (ConstructRef i n)
  | tProj p t => t' <- tsl_rec fuel Σ E Γ t ;;
                ret (tProj p t)

  | tFix bodies n =>
    Γ' <- monad_map (fun '{| dname := na; dtype := ty; dbody := b; rarg := r |} =>
                      ty' <- tsl_rec fuel Σ E Γ ty ;;
                      ret {| decl_name := na; decl_body := None; decl_type := ty'|})
                   bodies;;
    bodies' <- monad_map (fun '{| dname := na; dtype := ty; dbody := b; rarg := r |} =>
                           ty' <- tsl_rec fuel Σ E Γ ty ;;
                           b'  <- tsl_rec fuel Σ E (Γ ++ Γ')%list b ;;
                           ret {| dname := na; dtype := ty';
                                  dbody := b'; rarg := r |})
                        bodies ;;
    ret (tFix bodies' n)
  | _ => raise TranslationNotHandeled (* var evar meta case cofix *)
  end
  end.


(* Definition recompose_prod (nas : list name) (ts : list term) (u : term) *)
(*   : term *)
(*   := let nats := List.combine nas ts in *)
(*      List.fold_right (fun t u => tProd (fst t) (snd t) u) u nats. *)

Definition combine' {A B} (p : list A * list B)
  := List.combine  (fst p) (snd p).


Fixpoint replace pat u t {struct t} :=
  if eq_term uGraph.init_graph t pat then u else
    match t with
    | tCast t c A => tCast (replace pat u t) c (replace pat u A)
    | tProd n A B => tProd n (replace pat u A) (replace (up pat) (up u) B)
    | tLambda n A t => tLambda n (replace pat u A) (replace (up pat) (up u) t)
    | tLetIn n t A B => tLetIn n (replace pat u t) (replace pat u A)
                              (replace (up pat) (up u) B)
    | tApp t us => tApp (replace pat u t) (List.map (replace pat u) us)
    | tProj p t => tProj p (replace pat u t)
    | _ => t (* todo *)
    end.


(* If tm of type typ = Π [A0] [A1] ... . [B], returns *)
(* a term of type [Π A0 A1 ... . B] *)
Definition pouet (tm typ : term) : term.
  refine (let L := decompose_prod typ in _).
  simple refine (let L' := List.fold_left _ (combine' (fst L)) [] in _).
  exact (fun Γ' A => Γ' ,, vass (fst A) (snd A)).
  refine (let args := fold_left_i (fun l i _ => tRel i :: l) L' [] in _).
  refine (fst (List.fold_left _ L' (subst_app tm args, snd L))).
  refine (fun '(tm, typ) decl =>
            let A := tProd decl.(decl_name) decl.(decl_type) typ in
            (pairTrue A (tLambda decl.(decl_name) decl.(decl_type) tm),
             timesBool A)).
Defined.



Definition tsl_mind_body (ΣE : tsl_context) (mp : string) (kn : kername)
           (mind : mutual_inductive_body)
  : tsl_result (tsl_table * list mutual_inductive_body).
  refine (let tsl := fun Γ t => match tsl_rec fuel (fst ΣE) (snd ΣE) Γ t with
                             | Success x => x
                             | Error _ => todo
                             end in
          let kn' := tsl_kn tsl_ident kn mp in _).
  refine (let LI := List.split (map_i _ mind.(ind_bodies)) in
          ret (List.concat (fst LI),
               [{| ind_npars := mind.(ind_npars);
                   ind_bodies := snd LI;
                   ind_universes := mind.(ind_universes)|}])). (* FIXME always ok? *)
  intros i ind.
  simple refine (let ind_type' := _ in
                 let ctors' := List.split (map_i _ ind.(ind_ctors)) in
                 (_ :: fst ctors',
                  {| ind_name := tsl_ident ind.(ind_name);
                     ind_type := ind_type';
                     ind_kelim := ind.(ind_kelim);
                     ind_ctors := snd ctors';
                     ind_projs := [] |})).
  + (* arity *)
    refine (let L := decompose_prod ind.(ind_type) in _).
    simple refine (let L' := List.fold_left _ (combine' (fst L)) [] in _).
    exact (fun Γ' A => Γ' ,, vass (fst A) (tsl Γ' (snd A))).
    refine (List.fold_left _ L' (snd L)).
    exact (fun t decl => tProd decl.(decl_name) decl.(decl_type) t).
  + (* constructors *)
    intros k ((name, typ), nargs).
    simple refine (let ctor_type' := _ in
                   ((ConstructRef (mkInd kn i) k,
                     pouet (tConstruct (mkInd kn' i) k []) _),
                    (tsl_ident name, ctor_type', nargs))).
    * refine (fold_left_i (fun t i _ => replace (proj1 (tRel i)) (tRel i) t)
                          mind.(ind_bodies) _).
      refine (let L := decompose_prod typ in _).
      simple refine (let L' := List.fold_left _ (combine' (fst L))
                                              [] in _).
      exact (fun Γ' A => Γ' ,, vass (fst A) (tsl Γ' (snd A))).
      refine (List.fold_left _ L' _).
      exact (fun t decl => tProd decl.(decl_name) decl.(decl_type) t).
      exact (match snd L with
             | tApp t us => tApp t (List.map (tsl L') us)
             | _ as t => t
             end).
    * refine (fold_left_i (fun t l _ => replace (tRel l) (tInd (mkInd kn' i) []) t)
                          mind.(ind_bodies) ctor_type').
  + (* table *)
    refine (IndRef (mkInd kn i), pouet (tInd (mkInd kn' i) []) ind_type').
Defined.

Open Scope prod_scope.

Instance tsl_fun : Translation
  := {| tsl_id := tsl_ident ;
        tsl_tm := fun ΣE => tsl_rec fuel (fst ΣE) (snd ΣE) [] ;
        tsl_ty := Some (fun ΣE => tsl_rec fuel (fst ΣE) (snd ΣE) []) ;
        tsl_ind := tsl_mind_body |}.


Tactic Notation "tSpecialize" ident(H) uconstr(t)
  := apply π1 in H; specialize (H t).
Tactic Notation "tIntro" ident(H)
  := refine (fun H => _; true).

Definition NotFunext :=
  ((forall (A B : Set) (f g : A -> B), (forall x:A, f x = g x) -> f = g) -> False).

Run TemplateProgram (TC <- TranslateRec emptyTC NotFunext ;;
                     tmDefinition "TC" TC ;;
                     Implement TC "notFunext" NotFunext).
Next Obligation. 
  unfold NotFunextᵗ; cbn in *.
  tIntro H. 
  tSpecialize H unit. tSpecialize H unit. 
  tSpecialize H (fun x => x; true). tSpecialize H (fun x => x; false). 
  tSpecialize H (fun x => eq_reflᵗ _ _; true).
  inversion H. 
Defined.

Run TemplateProgram (Implement TC "notη" ((forall (A B : Set) (f : A -> B), f = fun x => f x) -> False)).

Next Obligation.
  tIntro H. 
  tSpecialize H unit. tSpecialize H unit. 
  tSpecialize H (fun x => x; false). cbn in H.
  inversion H. 
Defined.

Require Import Vector Even.
Definition SS := S.
Run TemplateProgram (TC <- Translate emptyTC "nat" ;;
                     TC <- Translate TC "even" ;;
                     tmDefinition "TC2" TC).

Inductive foo :=
| bar : (nat -> foo) -> foo.
Definition bar' := bar.
Run TemplateProgram (TranslateRec TC2 bar').

Require Import MiniHoTT.
Module Axioms.

  Definition UIP := forall A (x y : A) (p q : x = y), p = q.


  Run TemplateProgram (tmQuoteRec UIP >>= tmPrint).

  Run TemplateProgram (TC <- TranslateRec emptyTC UIP ;;
                       tmDefinition "eqTC" TC).

  Definition eqᵗ_eq {A} x y
    : eqᵗ A x y -> x = y.
  Proof.
    destruct 1; reflexivity.
  Defined.

  Definition eq_eqᵗ {A} x y
    : x = y -> eqᵗ A x y.
  Proof.
    destruct 1; reflexivity.
  Defined.

  Definition isequiv_eqᵗ_eq {A} x y
    : IsEquiv (@eqᵗ_eq A x y).
  Proof.
    unshelve eapply isequiv_adjointify.
    apply eq_eqᵗ.
    all: intros []; reflexivity.
  Defined.

  Theorem preserves_UIP : UIP -> UIPᵗ.
  Proof.
    unfold UIP, UIPᵗ.
    intros H.
    tIntro A. tIntro x. tIntro y. tIntro p. tIntro q.
    cbn in *.
    apply eq_eqᵗ. refine (equiv_inj _ (H := isequiv_eqᵗ_eq _ _) _).
    apply H.
  Defined.

  
  Definition wFunext
    := forall A (B : A -> Type) (f g : forall x, B x), (forall x, f x = g x) -> f = g.
 

  Open Scope prod_scope.
  Run TemplateProgram (TC <- TranslateRec eqTC (wFunext -> False) ;;
                       tmDefinition "eqTC'" TC ;;
                       Implement TC "notwFunext" (wFunext -> False)).
  Next Obligation.
    tIntro H.
    tSpecialize H unit. tSpecialize H (fun _ => unit; true). 
    tSpecialize H (fun x => x; true). tSpecialize H (fun x => x; false). 
    tSpecialize H (fun x => eq_reflᵗ _ _; true).
    inversion H. 
  Defined.

  Definition wUnivalence
    := forall A B, Equiv A B -> A = B.
 
  Run TemplateProgram (TC <- Translate eqTC' "idpath" ;;
                            TC <- ImplementExisting TC "paths_ind" ;;
                            tmDefinition "eqTC''" TC).
  Next Obligation.
    tIntro A. tIntro a. tIntro P. tIntro t.
    tIntro y. tIntro p. destruct p. exact t.
  Defined.

  Run TemplateProgram (TC <- TranslateRec eqTC'' (wUnivalence -> False) ;;
                       Implement TC "notwUnivalence" (wUnivalence -> False)).
  Next Obligation.
  Admitted.

End Axioms.