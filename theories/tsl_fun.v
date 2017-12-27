Require Import Template.Template Template.Ast Template.sigma.
Require Import Template.Induction Template.LiftSubst Template.Typing Template.Checker.
Require Import  Template.translation_utils.
Import String Lists.List.ListNotations MonadNotation.
Open Scope list_scope. Open Scope string_scope.


Fixpoint tsl_rec (fuel : nat) (Σ : global_context) (E : tsl_context) (Γ : context) (t : term) {struct fuel}
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
  | tApp (tInd i) u => u' <- monad_map (tsl_rec fuel Σ E Γ) u ;;
                      ret (tApp (tInd i) u')
  | tApp (tConstruct i n) u => u' <- monad_map (tsl_rec fuel Σ E Γ) u ;;
                              ret (tApp (tConstruct i n) u')
  | tApp t u => t' <- tsl_rec fuel Σ E Γ t ;;
               u' <- monad_map (tsl_rec fuel Σ E Γ) u ;;
               ret (tApp (proj1 t') u')
  | tConst s => match lookup_tsl_ctx E (ConstRef s) with
               | Some t => ret t
               | None => raise (TranslationNotFound s)
               end
  | tInd _ as t
  | tConstruct _ _ as t => ret t
  | tProj p t => t' <- tsl_rec fuel Σ E Γ t ;;
                ret (tProj p t)
  | _ => raise TranslationNotHandeled (* var evar meta case fix cofix *)
  end end.

Instance tsl_fun_instance_term : Translation
  := {| tsl_tm := fun Σ E => tsl_rec fuel Σ E [] |}.

Instance tsl_fun_instance_type : TranslationType
  := {| tsl_typ := fun Σ E => tsl_rec fuel Σ E [] |}.


(* Definition tsl := fun Σ E => tsl_rec fuel Σ E []. *)
(* Definition tsl_type := tsl. *)


(* Fixpoint tsl_rec (fuel : nat) (Σ : global_context) (E : tsl_context) (Γ : context) (t : term) (cst : option ident) {struct fuel} *)
(*   : tsl_result term := *)
(*   match fuel with *)
(*   | O => raise NotEnoughFuel *)
(*   | S fuel => *)
(*   match t with *)
(*   | tRel  n => ret (tRel n) *)
(*   | tSort s => ret (tSort s) *)
(*   | tCast t c A => t' <- tsl_rec fuel Σ E Γ t ;; *)
(*                   A' <- tsl_rec fuel Σ E Γ A ;; *)
(*                   ret (tCast t' c A') *)
(*   | tProd n A B => A' <- tsl_rec fuel Σ E Γ A ;; *)
(*                   B' <- tsl_rec fuel Σ E (Γ ,, vass n A) B ;; *)
(*                   ret (timesBool (tProd n A' B')) *)
(*   | tLambda n A t => A' <- tsl_rec fuel Σ E Γ A ;; *)
(*                     t' <- tsl_rec fuel Σ E (Γ ,, vass n A) t ;; *)
(*                     match infer Σ (Γ ,, vass n A) t with *)
(*                     | Checked B => *)
(*                       B' <- tsl_rec fuel Σ E (Γ ,, vass n A) B ;;  *)
(*                       ret (pairTrue (tProd n A' B') (tLambda n A' t')) *)
(*                     | TypeError _ => raise TypingError *)
(*                     end *)
(*   | tLetIn n t A u => t' <- tsl_rec fuel Σ E Γ t ;; *)
(*                      A' <- tsl_rec fuel Σ E Γ A ;; *)
(*                      u' <- tsl_rec fuel Σ E (Γ ,, vdef n t A) u ;; *)
(*                      ret (tLetIn n t' A' u') *)
(*   | tApp t u => t' <- tsl_rec fuel Σ E Γ t ;; *)
(*                u' <- monad_map (tsl_rec fuel Σ E Γ) u ;; *)
(*                ret (tApp (proj1 t') u') *)
(*   | tConst s as t *)
(*   | tInd (mkInd s _) as t => if ... then ret t *)
(*                             else match lookup_tsl_ctx E s with *)
(*                                  | Some t => ret (tConst t) *)
(*                                  | None => raise (TranslationNotFound s) *)
(*                                  end *)
(*   | tConstruct _ _ as t => ret t *)
                              
(*   | tProj p t => t' <- tsl_rec fuel Σ E Γ t ;; *)
(*                 ret (tProj p t) *)
(*   | _ => raise TranslationNotHandeled *)
(*   end end. *)

(* Definition tsl := fun Σ E => tsl_rec 1000 Σ E []. *)
(* Definition tsl_type := fun Σ E => tsl_rec 1000 Σ E []. *)

(* Definition tsl_inductive_decl (Σ : global_context) (E : tsl_context) *)
(*            (id : ident) (m : minductive_decl) *)
(*   : tsl_result (global_context * tsl_context). *)
(*   simple refine (let id' := id ++ "ᵗ" in *)
(*                  let t := fun ΣE I => *)
(*                             let typ := I.(ind_type) in *)
(*                             typ' <- tsl_type Σ E typ ;; (* include ΣE ? *) *)
(*                             let I' := _ in *)
(*                             let ctors' := _ in *)
(*                             let projs' := _ in *)
(*                             ret (projs' ++ ctors' ++ I' :: (fst ΣE), *)
(*                                  (id, id') :: (snd ΣE))%list *)
(*                  in *)
(*                    monad_fold_left t m.(ind_bodies) ([], []) *)
(*                 ). *)

(* Quote Recursively Definition yy := Vector.t . *)


(* Quote Definition tBool := bool. *)
(* Quote Definition tTimes := prod'. *)
(* Definition timesBool (t : term) : term *)
(*   := tApp tTimes [ t ; tBool ]. *)
(* Quote Definition t:= true. *)
(* Quote Definition tPair := pair'. *)
(* Definition pair(A t : term) : term *)
(*   := tApp tPair [ A ; tBool ; t ; tTrue]. *)
(* (* Test Quote ((pair' _ _ 4).(snd')). *) *)
(* (* Make Definition x := (tProj (mkInd "Top.prod'" 0, 2, 1) *) *)
(* (*    (tApp (tConstruct (mkInd "Top.prod'" 0) 0) *) *)
(* (*       [tInd (mkInd "Coq.Init.Datatypes.bool" 0); *) *)
(* (*       tInd (mkInd "Coq.Init.Datatypes.nat" 0); *) *)
(* (*       tConstruct (mkInd "Coq.Init.Datatypes.bool" 0) 0; *) *)
(* (*       tApp (tConstruct (mkInd "Coq.Init.Datatypes.nat" 0) 1) *) *)
(* (*         [tApp (tConstruct (mkInd "Coq.Init.Datatypes.nat" 0) 1) *) *)
(* (*            [tApp (tConstruct (mkInd "Coq.Init.Datatypes.nat" 0) 1) *) *)
(* (*               [tApp (tConstruct (mkInd "Coq.Init.Datatypes.nat" 0) 1) *) *)
(* (*                  [tConstruct (mkInd "Coq.Init.Datatypes.nat" 0) 0]]]]])). *) *)
(* (* Test Quote (snd' (pair' _ _ 4)). *) *)
(* Definition fstProj (t : term) : term *)
(*   := tProj (mkInd "Template.trad.prod'" 0, 2, 0) t. *)


(* Fixpoint tsl_rec fuel (Σ : global_context) (E : tsl_context) (Γ : context) (t : term) {struct t} *)
(*   : term := *)
(*   match t with *)
(*   (* | tRel       : nat -> term *) *)
(*   | tRel n => tRel n *)
(*   (* | tVar       : ident -> term (** For free variables (e.g. in a goal) *) *) *)
(*   | tVar v => tVar v *)
(*   (* | tMeta      : nat -> term   (** NOTE: this can go away *) *) *)
(*   | tMeta n => tMeta n *)
(*   (* | tEvar      : nat -> list term -> term *) *)
(*   | tEvar n l => tEvar n (List.map (tsl_rec fuel Σ E Γ) l) *)
(*   (* | tSort      : sort -> term *) *)
(*   | tSort s => tSort s *)
(*   (* | tCast      : term -> cast_kind -> term -> term *) *)
(*   | tCast t c A => tCast (tsl_rec fuel Σ E Γ t) c (tsl_rec fuel Σ E Γ A) *)
(*   (* | tProd      : name -> term (** the type **) -> term -> term *) *)
(*   | tProd n A B => let A' := tsl_rec fuel Σ E Γ A in timesBool (tProd n A' (tsl_rec fuel Σ E (Γ ,, vass n A') B)) *)
(*   (* | tLambda    : name -> term (** the type **) -> term -> term *) *)
(*   | tLambda n A t => let A' := tsl_rec fuel Σ E Γ A in *)
(*                     let t' := tLambda n A' (tsl_rec fuel Σ E (Γ ,, vass n A') t) in *)
(*                     match infer Σ Γ t' with *)
(*                     | Checked A' => pairA' t' *)
(*                     | _ => (* FIXME *) tBool *)
(*                     end *)
(*     (* t' *) *)
(*   (* | tLetIn     : name -> term (** the term **) -> term (** the type **) -> term -> term *) *)
(*   | tLetIn n t A u => let t' := tsl_rec fuel Σ E Γ t in *)
(*                      let A' := tsl_rec fuel Σ E Γ A in *)
(*                      tLetIn n t' A' (tsl_rec fuel Σ E (Γ ,, vdef n t' A') u) *)
(*   (* | tApp       : term -> list term -> term *) *)
(*   | tApp (tInd i) u => tApp (tInd i) (List.map (tsl_rec fuel Σ E Γ) u) *)
(*   | tApp (tConstruct i n) u => tApp (tConstruct i n) (List.map (tsl_rec fuel Σ E Γ) u) *)
(*   | tApp t u => tApp (fstProj (tsl_rec fuel Σ E Γ t)) (List.map (tsl_rec fuel Σ E Γ) u) *)
(*   (* | tConst     : string -> term *) *)
(*   | tConst s => match lookup_tsl_ctx E s with *)
(*                | Some t => tConst t *)
(*                | None => (* FIXME *) tBool *)
(*                end *)
(*   (* | tInd       : inductive -> term *) *)
(*   | tInd i => tInd (tsl_inductive i) *)
(*   (* | tConstruct : inductive -> nat -> term *) *)
(*   | tConstruct i n => tConstruct (tsl_inductive i) n *)
(*   (* | tCase      : (inductive * nat) (* # of parameters *) -> term (** type info **) -> term -> *) *)
(*   (*                list (nat * term) -> term *) *)
(*   | tCase (i , n) t u l => tCase (tsl_inductive i , n) (tsl_rec fuel Σ E Γ t) (tsl_rec fuel Σ E Γ u) (List.map (fun nt => (fst nt , tsl_rec fuel Σ E Γ (snd nt))) l) *)
(*   (* | tProj      : projection -> term -> term *) *)
(*   | tProj p t => tProj (tsl_projection p) (tsl_rec fuel Σ E Γ t) *)
(*   (* | tFix       : mfixpoint term -> nat -> term *)  (* mfixpoint = list (def term) *) *)
(*   | tFix l n => tFix (List.map (map_def (tsl_rec fuel Σ E Γ)) l) n *)
(*   (* | tCoFix     : mfixpoint term -> nat -> term. *) *)
(*   | tCoFix l n => tCoFix (List.map (map_def (tsl_rec fuel Σ E Γ)) l) n *)
(*   end. *)

Tactic Notation "myeapply" constr(lemma) "unifying" open_constr(term) :=
  let TT := type of term in
  let T := open_constr:(_:TT) in
  replace term with T;
  [eapply lemma|].


Require Import Template.Checker.

Inductive squash (A : Type) : Prop :=
  | sq : A -> squash A.



Definition option_get {A} (default : A) (x : option A) : A
  := match x with
     | Some x => x
     | None => default
     end.

Definition map_context_decl (f : term -> tsl_result term) (decl : context_decl): tsl_result context_decl

  := b' <- (match decl.(decl_body) with
           | Some b => b' <- f b ;; ret (Some b')
           | None => ret None
           end) ;;
     t' <- f decl.(decl_type) ;;
     ret {| decl_name := decl.(decl_name);
            decl_body := b'; decl_type := t' |}.



Arguments Success {_} _.
Arguments Error {_} _.

Lemma map_context_decl_success f d d' (H : map_context_decl f d = Success d')
  : (decl_name d' = decl_name d) /\ (match decl_body d with
                                    | Some t => ex (fun t' => (decl_body d') = Some t' /\ Success t' = f t)
                                    | None => decl_body d' = None
                                    end)
    /\ (Success (decl_type d') = f (decl_type d)).
  destruct d as [n t A].
  change ((b' <- (match t with
           | Some b => b' <- f b ;; ret (Some b')
           | None => ret None
           end) ;;
     t' <- f A ;;
     ret {| decl_name := n;
            decl_body := b'; decl_type := t' |}) = Success d') in H.
  destruct t.
  - remember (f t). destruct t0; [|discriminate].
    remember (f A). destruct t1; [|discriminate].
    cbn in H. inversion H. cbn.
    split. reflexivity. split; [|assumption].
    exists t0. split. reflexivity. assumption.
  - remember (f A). destruct t; [|discriminate].
    cbn in H. inversion H. cbn.
    split. reflexivity. split; [|assumption].
    reflexivity.
Qed.


  
Fixpoint tsl_ctx (fuel : nat) (Σ : global_context) (E : tsl_context) (Γ : context) : tsl_result context
  := match Γ with
     | [] => ret []
     | A :: Γ => A' <- map_context_decl (tsl_rec fuel Σ E Γ) A ;;
                Γ' <- (tsl_ctx fuel Σ E Γ) ;;
                ret (A' :: Γ')
     end.

Lemma le_irr n m (p q : n <= m) : p = q.
Admitted.

Lemma tsl_ctx_cons fuel Σ E Γ A
  : tsl_ctx fuel Σ E (A :: Γ)
    = (A' <- map_context_decl (tsl_rec fuel Σ E Γ) A ;;
       Γ' <- (tsl_ctx fuel Σ E Γ) ;;
       ret (A' :: Γ')).
  reflexivity.
Defined.

  
Lemma tsl_ctx_length fuel Σ E Γ
  : forall Γ', tsl_ctx fuel Σ E Γ = Success Γ' -> #|Γ| = #|Γ'|.
Proof.
  induction Γ; intros Γ' H.
  - destruct Γ'. reflexivity. discriminate.
  - rewrite tsl_ctx_cons in H.
    remember (map_context_decl (tsl_rec fuel Σ E Γ) a). 
    destruct t; [|discriminate].
    remember (tsl_ctx fuel Σ E Γ). 
    destruct t; [|discriminate].
    cbn in H. inversion H; clear H.
    cbn. apply eq_S. apply IHΓ. reflexivity.
Defined.

Fixpoint removefirst_n {A} (n : nat) (l : list A) : list A :=
  match n with
  | O => l
  | S n => match l with
          | [] => []
          | a :: l => removefirst_n n l
          end
  end.

Notation "( x ; y )" := (exist _ x y).

Lemma tsl_ctx_safe_nth fuel Σ E Γ
  : forall Γ', tsl_ctx fuel Σ E Γ = Success Γ' -> forall n p, exists p',
        map_context_decl (tsl_rec fuel Σ E (removefirst_n (S n) Γ))
                         (safe_nth Γ (n; p))
        = Success (safe_nth Γ' (n; p')).
  intros Γ' H n p. cbn beta in *.
  revert Γ Γ' H p.
  induction n; intros Γ Γ' H p;
    (destruct Γ as [|A Γ]; [inversion p|]).
  - cbn -[map_context_decl].
    rewrite tsl_ctx_cons in H.
    remember (map_context_decl (tsl_rec fuel Σ E Γ) A). 
    destruct t; [|discriminate].
    remember (tsl_ctx fuel Σ E Γ). 
    destruct t; [|discriminate].
    cbn in H. inversion H; clear H.
    clear p H1.
    unshelve econstructor. apply le_n_S, le_0_n.
    reflexivity.
  - cbn -[map_context_decl].
    rewrite tsl_ctx_cons in H.
    remember (map_context_decl (tsl_rec fuel Σ E Γ) A). 
    destruct t; [|discriminate].
    remember (tsl_ctx fuel Σ E Γ). 
    destruct t; [|discriminate].
    cbn in H. inversion H; clear H.
    symmetry in Heqt0.
    set (Typing.safe_nth_obligation_2 context_decl (A :: Γ) (S n; p) A Γ eq_refl n eq_refl).
    specialize (IHn Γ c0 Heqt0 l).
    destruct IHn.
    
    unshelve econstructor.
    cbn. rewrite <- (tsl_ctx_length fuel Σ E Γ _ Heqt0). exact p.
    etransitivity. exact π2. cbn.
    apply f_equal, f_equal, f_equal.
    apply le_irr.
Defined.


(* (* todo inductives *) *)
(* Definition global_ctx_correct (Σ : global_context) (E : tsl_context) *)
(*   := forall id T, lookup_constant_type Σ id = Checked T *)
(*                 -> exists fuel t' T', lookup_tsl_ctx E (ConstRef id) = Some t' /\ *)
(*                            tsl_rec fuel Σ E [] T = Success _ T' /\ *)
(*                            squash (Σ ;;; [] |-- t' : T'). *)


Definition tsl_ctx_correct Σ E
  := forall id t' T,
    lookup_tsl_ctx E (ConstRef id) = Some t' ->
    lookup_constant_type Σ id = Checked T ->
    exists fuel T', ((tsl_rec fuel Σ E [] T = Success T')
      * (Σ ;;; [] |--  t' : T'))%type.

Lemma tsl_lift fuel Σ E Γ n (p : n <= #|Γ|) t
  : tsl_rec fuel Σ E Γ (lift0 n t) =
    (t' <- tsl_rec fuel Σ E (removefirst_n n Γ) t ;; ret (lift0 n t')).
Admitted.

Lemma tsl_S_fuel {fuel Σ E Γ t t'}
  : tsl_rec fuel Σ E Γ t = Success t' -> tsl_rec (S fuel) Σ E Γ t = Success t'.
Admitted.


Lemma tsl_correct Σ Γ t T (H : Σ ;;; Γ |-- t : T)
  : forall E, tsl_ctx_correct Σ E ->
    forall fuel Γ' t' T',
    tsl_rec fuel Σ E Γ t = Success t' ->
    tsl_rec fuel Σ E Γ T = Success T' ->
    tsl_ctx fuel Σ E Γ = Success Γ' -> Σ ;;; Γ' |-- t' : T'.
  induction H; intros;
    (destruct fuel; [discriminate|]).
  - inversion H0.
    destruct (tsl_ctx_safe_nth _ Σ E Γ _ H2 n isdecl) as [p H3].
    unshelve myeapply type_Rel unifying T'. assumption.
    apply map_context_decl_success in H3.
    destruct H3 as [_ [_ H3]].
    assert (Success (lift0 (S n) (decl_type (safe_nth Γ' (n; p))))
            = Success T'). {
      etransitivity; [|eassumption].
      clear -H3. rewrite tsl_lift. now rewrite <- H3. assumption.
    }
    now inversion H5.
  - inversion H0. clear H0 H4.
    inversion H1. econstructor.
  - cbn in H2.
    remember (tsl_rec fuel Σ E Γ c).
    destruct t0; [|discriminate].
    remember (tsl_rec fuel Σ E Γ t).
    destruct t1; [|discriminate].
    inversion H2; clear H2. clear t' H6.
    myeapply type_Cast unifying T'.
    + eapply IHtyping1 ; try eassumption.
      2: reflexivity. now apply tsl_S_fuel.
    + eapply IHtyping2; try eassumption;
        now apply tsl_S_fuel.
    + symmetry in Heqt1. apply tsl_S_fuel in Heqt1.
      rewrite Heqt1 in H3. now inversion H3.
  - cbn in H3. cbn in H2.
    inversion H3. clear H3 H6.
    remember (tsl_rec fuel Σ E Γ t).
    destruct t0; [|discriminate].
    remember (tsl_rec fuel Σ E (Γ,, vass n t) b).
    destruct t1; [|discriminate].
    inversion H2. clear H2 H5.
    unfold timesBool.
    symmetry in Heqt0, Heqt1.
    specialize (IHtyping1 E H1 (S fuel) Γ' t0 (tSort s1) (tsl_S_fuel Heqt0) eq_refl H4).
    specialize (IHtyping2 E H1 (S fuel) (Γ' ,,vass n t0) t1 (tSort s2) (tsl_S_fuel Heqt1) eq_refl).
    simple refine (let IH2 := IHtyping2 _ in _);
      [|clearbody IH2; clear IHtyping2].
    { unfold snoc. rewrite tsl_ctx_cons.
      rewrite H4. cbn -[tsl_rec].
      rewrite (tsl_S_fuel Heqt0). reflexivity. }
    pose proof (type_Prod  _ _ _ _ _ _ _ IHtyping1 IH2).
    clear -H2.
    eapply type_App. unfold tSigma.
    eapply type_Ind. econstructor.

