(* -*- coq-prog-args : ("-debug" "-type-in-type") -*-  *)

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
Open Scope list_scope.
Open Scope sigma_scope.


(* Definition t := Type -> Type. *)
(* Translate t. *)

Implement toto : Type -> Type.
cbn. unshelve econstructor.
Abort.

Notation "'tΣ'" := (tInd (mkInd "Template.sigma.sigma" 0)).
Notation "'tproj1'" := (tProj (mkInd "Template.sigma.sigma" 0, 2, 0)).
Notation "'tImpl'" := (tProd nAnon).


Definition tsl_ident (id : ident) : ident := (id ++ "ᵗ")%string.

Definition tsl_inductive (ind : inductive) : inductive.
  destruct ind. exact (mkInd (tsl_ident s) n).
Defined.

Axiom todo_coq : forall {X}, X.


Quote Recursively Definition sigma_prog := @sigma.
Quote Recursively Definition eq_prog := @eq.


Fixpoint fold_left_i_aux {A B} (f : A -> nat -> B -> A) (n0 : nat) (l : list B)
         (a0 : A) {struct l} : A
  := match l with
     | [] => a0
     | b :: l => fold_left_i_aux f (S n0) l (f a0 n0 b)
     end.
Definition fold_left_i {A B} f := @fold_left_i_aux A B f 0.


Fixpoint extract_mind_decl_from_program (id : ident) (p : program)
  : option minductive_decl
  := match p with
     | PConstr _ _ _ p => extract_mind_decl_from_program id p
     | PType id' n inds p => if string_dec id id' then
                              Some (Build_minductive_decl n inds)
                            else extract_mind_decl_from_program id p
     | PAxiom _ _ p => extract_mind_decl_from_program id p
     | PIn _ => None
     end.


Inductive eq' (A : Set) (x : A) : A -> Prop :=  eq_refl' : eq' A x x.
Quote Recursively Definition eq'_prog := eq'.

Definition eq'_decl := Eval compute in
      extract_mind_decl_from_program "Top.eq'" eq'_prog.
Definition eq_decl := Eval compute in
      extract_mind_decl_from_program "Coq.Init.Logic.eq" eq_prog.
Definition sigma_decl := Eval compute in
      extract_mind_decl_from_program "Template.sigma.sigma" sigma_prog.


Fixpoint decompose_prod (t : term) : (list name) * (list term) * term :=
  match t with
  | tProd n A B => let (nAs, B) := decompose_prod B in
                  let (ns, As) := nAs in
                  (n :: ns, A :: As, B)
  | _ => ([], [], t)
  end.

Fixpoint recompose_prod (ns : list name) (As : list term) (B : term) : term :=
  match (ns, As) with
  | (n :: ns, A :: As)  => tProd n A (recompose_prod ns As B)
  | _ => B
  end.


Fixpoint remove_arity (n : nat) (t : term) : term :=
  match n with
  | O => t
  | S n => match t with
          | tProd _ _ B => remove_arity n B
          | _ => t (* todo *)
          end
  end.


Definition get_ident (n : name) :=
  match n with
  | nAnon => "XX"
  | nNamed i => i
  end.

Definition mind_decl_to_entry (* (id : ident) *) (decl : minductive_decl)
  : mutual_inductive_entry.
Proof.
  refine ({|
             mind_entry_record := None; (* not a record *)
             mind_entry_finite := Finite; (* inductive *)
             mind_entry_params := _;
             mind_entry_inds := _;
             mind_entry_polymorphic := false;
             mind_entry_private := None;
           |}).
  - refine (match List.hd_error decl.(ind_bodies) with
            | Some i0 => _
            | None => nil (* todo *)
            end).
    pose (typ := decompose_prod i0.(ind_type)).
    destruct typ as [[names types] _].
    apply (List.firstn decl.(ind_npars)) in names.
    apply (List.firstn decl.(ind_npars)) in types.
    refine (List.rev (List.combine _ _)).
    exact (List.map get_ident names).
    exact (List.map LocalAssum types).
    (* pose (fold_left_i (fun acc i ty => let na := tVar (get_ident (List.nth i names nAnon)) *)
    (*                                 in (na :: fst acc, substl (fst acc) ty :: snd acc)) types ([], [])). *)
    (* exact (snd p). *)
  - refine (List.map _ decl.(ind_bodies)).
    intros [].
    refine ({| mind_entry_typename := ind_name;
               mind_entry_arity := remove_arity decl.(ind_npars) ind_type;
               mind_entry_template := false;
               mind_entry_consnames := _;
               mind_entry_lc := _;
            |}).
    
    refine (List.map (fun x => fst (fst x)) ind_ctors).
    refine (List.map (fun x => remove_arity decl.(ind_npars)
                                                (snd (fst x))) ind_ctors).
Defined.

Definition option_get {A} (default : A) (x : option A) : A
  := match x with
     | Some x => x
     | None => default
     end.

Definition eq_entry := Eval compute in
      (mind_decl_to_entry (option_get todo_coq eq_decl)).
Definition sigma_entry := Eval compute in
      (mind_decl_to_entry (option_get todo_coq sigma_decl)).

(* Make Inductive eq_entry. *)
(* Make Inductive sigma_entry. *)

Require Vectors.VectorDef.
Quote Recursively Definition vect_prog := Vectors.VectorDef.t.
Definition vect_decl := Eval compute in
      extract_mind_decl_from_program "Coq.Vectors.VectorDef.t" vect_prog.
Definition vect_entry := Eval compute in
      (mind_decl_to_entry (option_get todo_coq vect_decl)).
(* Make Inductive vect_entry. *)
(* Inductive t (A : Type) : nat -> Type := *)
    (* nil : t A 0 | cons : A -> forall n : nat, t A n -> t A (S n) *)


Inductive boolR : bool -> Set :=
| trueR : boolR true
| falseR : boolR false.

Definition boolT := sigma bool boolR.

Inductive IsTrue (b : bool) : bool -> Type :=
| tiptop : IsTrue b true.
Open Scope sigma_scope.

Inductive IsTrueR (b : boolT) : forall (b' : boolT), IsTrue b.1 b'.1 -> Type :=
| tiptopR : IsTrueR b (true; trueR) (tiptop b.1).



Quote Recursively Definition nat_prog := nat.
Definition nat_entry := Eval compute in 
      (mind_decl_to_entry
         (option_get todo_coq
                     (extract_mind_decl_from_program "Coq.Init.Datatypes.nat" nat_prog)
      )).

Require Import Even.
Quote Recursively Definition even_prog := even.
Definition even_entry := Eval compute in 
      (mind_decl_to_entry
         (option_get todo_coq
                     (extract_mind_decl_from_program "Coq.Arith.Even.even" even_prog)
      )).
(* Make Inductive even_entry. *)
(* Inductive even : nat -> Prop := *)
(*     even_O : even 0 | even_S : forall n : nat, odd n -> even (S n) *)
(*   with odd : nat -> Prop :=  odd_S : forall n : nat, even n -> odd (S n) *)


Quote Recursively Definition bool_prog := bool.
Definition bool_entry := Eval compute in 
      (mind_decl_to_entry
         (option_get todo_coq
                     (extract_mind_decl_from_program "Coq.Init.Datatypes.bool" bool_prog)
      )).

Quote Recursively Definition istrue_prog := @IsTrue.
Definition istrue_entry := Eval compute in 
      (mind_decl_to_entry
         (option_get todo_coq
                     (extract_mind_decl_from_program "Top.IsTrue" istrue_prog)
      )).

Quote Recursively Definition istruer_prog := @IsTrueR.
Definition istruer_entry := Eval compute in 
      (mind_decl_to_entry
         (option_get todo_coq
                     (extract_mind_decl_from_program "Top.IsTrueR" istruer_prog)
      )).

Definition istruer_entry' :=
  {|
mind_entry_record := None;
mind_entry_finite := Finite;
mind_entry_params := [("b", LocalAssum (tConst "Top.boolT"))];
mind_entry_inds := [{|
                    mind_entry_typename := "IsTrueR'";
                    mind_entry_arity := tProd (nNamed "b'")
                                          (tConst "Top.boolT")
                                          (tProd nAnon
                                             (tApp
                                                (tInd
                                                (mkInd "Top.IsTrue" 0))
                                                [
                                                tProj
                                                (
                                                mkInd
                                                "Template.sigma.sigma" 0,
                                                2, 0) 
                                                (tRel 1);
                                                tProj
                                                (
                                                mkInd
                                                "Template.sigma.sigma" 0,
                                                2, 0) 
                                                (tRel 0)]) 
                                             (tSort sProp));
                    mind_entry_template := false;
                    mind_entry_consnames := ["tiptopR'"];
                    mind_entry_lc := [tApp (tRel 1)
                                        [tRel 0;
                                        tApp
                                          (tConstruct
                                             (mkInd "Template.sigma.sigma"
                                                0) 0)
                                          [tInd
                                             (mkInd
                                                "Coq.Init.Datatypes.bool"
                                                0);
                                          tInd (mkInd "Top.boolR" 0);
                                          tConstruct
                                            (mkInd
                                               "Coq.Init.Datatypes.bool" 0)
                                            0;
                                          tConstruct 
                                            (mkInd "Top.boolR" 0) 0];
                                        tApp
                                          (tConstruct
                                             (mkInd "Top.IsTrue" 0) 0)
                                          [tProj
                                             (mkInd "Template.sigma.sigma"
                                                0, 2, 0) 
                                             (tRel 0)]]] |}];
mind_entry_polymorphic := false;
mind_entry_private := None |}.
Make Inductive istruer_entry'.




(* Definition pair_map {A A' B B'} (f : A -> A') (g : B -> B') *)
(*   : A * B -> A' * B' *)
(*   := fun w => (f (fst w), g (snd w)). *)

(* Definition tsl_ctor : (ident * term * nat) -> (ident * term * nat). *)
(*   intros [[id typ] k]. *)
(*   refine ((tsl_ident id, _), _). *)
(* Admitted. *)

Fixpoint from_n {A} (f : nat -> A) (n : nat) : list A :=
  match n with
  | O => []
  | S n => f n :: (from_n f n)
  end.

Fixpoint map_i_aux {A B} (f : nat -> A -> B) (n0 : nat) (l : list A) : list B
  := match l with
     | [] => []
     | x :: l => (f n0 x) :: (map_i_aux f (S n0) l)
     end.

Definition map_i {A B} f := @map_i_aux A B f 0.


(* Definition tsl_one_entry (Σ : global_context) (E : tsl_context) *)
(*            (i : inductive) (ind : inductive_body) *)
(*   : inductive_body * tsl_context. *)
(*   refine (let tsl_ty' := fun t => match tsl_typ Σ E t with *)
(*                                | Success _ t => t *)
(*                                | Error _ _ => todo_coq *)
(*                                end in _). *)
(*   refine (let tsl_rec2' := fun t => match tsl_rec2 fuel Σ E [] t with *)
(*                                  | Success _ t => t *)
(*                                  | Error _ _ => todo_coq *)
(*                                  end in _). *)
(*   destruct ind. pose (i' := tsl_inductive i). split. *)
(*   - econstructor. *)
(*     + exact (tsl_ident ind_name). *)
(*     + refine (let (nAs, u) := decompose_prod ind_type in *)
(*               let (ns, As) := nAs in _). *)
(*       refine (let As' := List.map tsl_ty' As in _). *)
(*       refine (recompose_prod (ns ++ [nAnon]) (As' ++ [_]) u). *)
(*       refine (tApp (tInd i) _). *)
(*       refine (from_n (fun n => proj1 (tRel n)) (List.length As)). *)
(*     + assumption. *)
(*     + refine (List.map tsl_ctor ind_ctors). *)
(*     + exact []. (* todo projs *) *)
(*   - refine (_ (* ind  *):: _ (* ctors *) ++ _ (* projs *))%list. *)
(*     + refine (IndRef i, _). *)
(*       exact (pair ind_type (tsl_rec2' ind_type) *)
(*                   (tInd i) (tInd i')). *)
(*     + refine (map_i _ ind_ctors). *)
(*       intros k [[_ typ] _]. refine (ConstructRef i k, _). *)
(*       refine (pair _ _ (tConstruct i k) (tConstruct i' k)). *)
(*       all: exact todo_coq. (* TODO *) *)
(*     + exact []. (* todo projs *) *)
(* Defined. *)

Definition mkImpl (A B : term) : term :=
  tProd nAnon A B.


Definition local_entry_map (f : term -> term) (m : local_entry) : local_entry
  := match m with
     | LocalDef t => LocalDef (f t)
     | LocalAssum t => LocalAssum (f t)
     end.

Open Scope list_scope.

Definition mkApp t us :=
  match us with
  | nil => t
  | _ => tApp t us
  end.

Definition get_local_entry (l : local_entry) : term :=
  match l with
  | LocalDef t => t
  | LocalAssum t => t
  end.

Definition recompose_prod' (l : list (ident * local_entry)
                           (* Xn at the head of the list *))
           (b : term) : term.
  apply List.rev in l.
  eapply List.split in l. eapply recompose_prod.
  exact (List.map nNamed (fst l)).
  exact (List.map get_local_entry (snd l)).
  exact b.
Defined.

Definition tsl_mind_entry  (Σ : global_context) (E : tsl_context)
           (id : ident) (mind : mutual_inductive_entry)
  : mutual_inductive_entry.
  refine (let tsl_ty' := fun t => match tsl_typ Σ E t with
                               | Success _ t => t
                               | Error _ _ => todo_coq
                               end in _).
  refine (let tsl_tm' := fun t => match tsl_tm Σ E t with
                               | Success _ t => t
                               | Error _ _ => todo_coq
                               end in _).
  (* refine (let tsl2' := fun t : term => t in _). *)
  refine (let tsl2' := fun t : term => match tsl_rec2 fuel Σ E [] t with
                                    | Success _ t => t
                                    | Error _ _ => todo_coq
                                    end in _).
  refine {| mind_entry_record := mind.(mind_entry_record);
            mind_entry_finite := mind.(mind_entry_finite);
            mind_entry_params := _;
            mind_entry_inds := _;
            mind_entry_polymorphic := mind.(mind_entry_polymorphic);
            mind_entry_private := mind.(mind_entry_private);
         |}.
  refine (List.map (fun x => (fst x, local_entry_map tsl_ty' (snd x)))
                   mind.(mind_entry_params)).
  simple refine (let L : list term := _ ++ _ in _).
  refine (map_i (fun i _ => tRel i) mind.(mind_entry_params)).
  pose (l := List.length mind.(mind_entry_params)).
  pose (p := List.length mind.(mind_entry_inds)-1).
  simple refine (map_i (fun i _ => let arity_i := _ in
                                pair arity_i _ (tInd (mkInd id (p-i))) (tRel (l+i)))
                       mind.(mind_entry_inds)). 
  refine (recompose_prod'
            mind.(mind_entry_params)
                   (List.nth (p-i) mind.(mind_entry_inds) todo_coq).(mind_entry_arity)).
  (* refine (mkApp (tsl2' arity_i) [tInd (mkInd id (p-i))]). *)
  refine (tsl2' arity_i).

  refine (map_i _ mind.(mind_entry_inds)).
  intros i ind.
  simple refine {| mind_entry_typename := tsl_ident (ind.(mind_entry_typename));
                   mind_entry_arity := _;
                   mind_entry_template := ind.(mind_entry_template);
                   mind_entry_consnames := List.map tsl_ident ind.(mind_entry_consnames);
                   mind_entry_lc := _;
                |}.
  - refine (tApp _ [_]).
    exact (tsl2' ind.(mind_entry_arity)).
    refine (mkApp (tInd (mkInd id i)) _).
    refine (from_n (fun n => proj1 (tRel n))
                   (List.length mind.(mind_entry_params))).
  (* - pose (arity := decompose_prod ind.(mind_entry_arity)). *)
  (*   destruct arity as [[ns As] u]. *)
  (*   refine (let As' := List.map tsl_ty' As in _). *)
  (*   refine (recompose_prod ns As' (mkImpl _ u)). *)
  (*   refine (mkApp (tInd (mkInd id i)) _). *)
  (*   refine (List.rev (from_n (fun n => proj1 (tRel n)) (List.length mind.(mind_entry_params) + List.length As))). *)
  - refine (map_i _ ind.(mind_entry_lc)).
    intros k t.
    refine (tApp _ [_]).
    refine (substl L (tsl2' t)).
    (* pose (l := (List.length mind.(mind_entry_params)) + 0 (* todo *)). *)
    (* refine (subst _ l (tsl2' Σ t)). *)
    (* pose (whole_arity := recompose_prod' mind.(mind_entry_params) *)
    (*                                             ind.(mind_entry_arity)). *)
    (* refine (pair whole_arity (tsl2' Σ whole_arity) (tInd (mkInd id i)) (tRel l)). *)
    refine (mkApp (tConstruct (mkInd id i) k) _).
    refine (from_n (fun n => proj1 (tRel n))
                   (List.length mind.(mind_entry_params))).
    
    (* pose (a := decompose_prod t). *)
    (* destruct a as [[ns As] u]. *)
    (* simple refine (let As' : list term := map_i _ As in _). *)
    (* (* refine (fun l t => match t with tRel l' => if EqNat.eq_nat_decide l l' then (tApp (tInd (mkInd "Template.sigma.sigma" 0)) [tInd (mkInd id 0); t]) else tsl_ty' t | _ => tsl_ty' t end). *) *)
    (* (* refine (fun l t => subst (tApp tΣ [tInd (mkInd id 0); tRel l]) l (tsl_ty' t)). *) *)
    (* refine (fun l t => subst (pair ind.(mind_entry_arity) arity' (tInd (mkInd id 0 (* todo 0? *))) (tRel l)) l (tsl_ty' t)). *)
    (* refine (recompose_prod ns As' _). *)
    (* (* simple refine (recompose_prod ns (List.map tsl_ty' As) _). *) *)
    (* refine (let bla := _ in *)
    (*         match u with *)
    (*         | tApp u1 us2 => tApp u1 ((List.map tsl_tm' us2) ++ [bla]) *)
    (*         | tRel n => tApp (tRel n) [bla] *)
    (*         | _ => todo_coq *)
    (*         end). *)
    (* refine (mkApp (tConstruct (mkInd id i) k) _). *)
    (* refine (List.rev (from_n (fun n => proj1 (tRel n)) (List.length mind.(mind_entry_params) + List.length As))). *)
Defined.



Definition bool_entryT := Eval vm_compute in tsl_mind_entry [] [] "Coq.Init.Datatypes.bool" bool_entry.
Make Inductive bool_entryT.

Definition eq_entryT := Eval vm_compute in tsl_mind_entry [] [] "Coq.Init.Datatypes.eq" eq_entry.
Definition eq'_entry := Eval compute in
      (mind_decl_to_entry (option_get todo_coq eq'_decl)).
Definition eq'_entryT := Eval vm_compute in tsl_mind_entry [] [] "Top.eq'" eq'_entry.
(* Make Inductive eq'_entryT. *)
(* Check eq'ᵗ. *)

Definition nat_entryT := Eval vm_compute in tsl_mind_entry [] [] "Coq.Init.Datatypes.nat" nat_entry.
Make Inductive nat_entryT.
Check (natᵗ : nat -> Set).
Check (Oᵗ : natᵗ O).
Check (Sᵗ : forall (N : exists n, natᵗ n), natᵗ (S N.1)).

Inductive list (A : Set) : Set :=
    nil : list A | cons : A -> list A -> list A.
Quote Recursively Definition list_prog := @list.
Definition list_entry := Eval compute in 
      (mind_decl_to_entry
         (option_get todo_coq
                     (extract_mind_decl_from_program "Top.list" list_prog))).
Definition list_entryT := Eval vm_compute in tsl_mind_entry [] [] "Top.list" list_entry.
Make Inductive list_entryT.

Definition list_entryT' := {|
mind_entry_record := None;
mind_entry_finite := Finite;
mind_entry_params := [("A",
                      LocalAssum
                        (tApp tΣ
                           [tSort sSet;
                           tLambda (nNamed "A") (tSort sSet)
                             (tImpl (tRel 0) (tSort sSet))]))];
mind_entry_inds := [{|
                    mind_entry_typename := "listᵗ";
                    mind_entry_arity := tApp
                                          (tLambda 
                                             (nNamed "A") 
                                             (tSort sSet)
                                             (tImpl (tRel 0) (tSort sSet)))
                                          [tApp (tInd (mkInd "Top.list" 0))
                                             [tproj1 (tRel 0)]];
                    mind_entry_template := false;
                    mind_entry_consnames := ["nilᵗ"; "consᵗ"];
                    mind_entry_lc := [tApp
                                        (tApp
                                           (tProj
                                              (mkInd "Template.sigma.sigma"
                                                 0, 2, 1)
                                              (tApp
                                                 (tConstruct
                                                 (mkInd
                                                 "Template.sigma.sigma" 0) 0)
                                                 [
                                                 tProd 
                                                 (nNamed "A") 
                                                 (tSort sSet) 
                                                 (tSort sSet);
                                                 tLambda 
                                                 (nNamed "f")
                                                 (tProd 
                                                 (nNamed "A") 
                                                 (tSort sSet) 
                                                 (tSort sSet))
                                                 (tProd 
                                                 (nNamed "A")
                                                 (tApp 
                                                 tΣ
                                                 [
                                                 tSort sSet;
                                                 tLambda 
                                                 (nNamed "A") 
                                                 (tSort sSet)
                                                 (tImpl 
                                                 (tRel 0) 
                                                 (tSort sSet))])
                                                 (tApp
                                                 (tLambda 
                                                 (nNamed "A") 
                                                 (tSort sSet)
                                                 (tImpl 
                                                 (tRel 0) 
                                                 (tSort sSet)))
                                                 [
                                                 tApp 
                                                 (tRel 1) 
                                                 [tproj1 (tRel 0)]]));
                                                 tInd (mkInd "Top.list" 0);
                                                 tRel 2])) 
                                           [tRel 0])
                                        [tApp
                                           (tConstruct 
                                              (mkInd "Top.list" 0) 0)
                                           [tproj1 (tRel 0)]];
                                     tApp
                                       (tLambda (nNamed "f")
                                          (tImpl (tproj1 (tRel 0))
                                             (tImpl
                                                (tApp
                                                 (tproj1
                                                 (tApp
                                                 (tConstruct
                                                 (mkInd
                                                 "Template.sigma.sigma" 0) 0)
                                                 [
                                                 tProd 
                                                 (nNamed "A") 
                                                 (tSort sSet) 
                                                 (tSort sSet);
                                                 tLambda 
                                                 (nNamed "f")
                                                 (tProd 
                                                 (nNamed "A") 
                                                 (tSort sSet) 
                                                 (tSort sSet))
                                                 (tProd 
                                                 (nNamed "A")
                                                 (tApp 
                                                 tΣ
                                                 [
                                                 tSort sSet;
                                                 tLambda 
                                                 (nNamed "A") 
                                                 (tSort sSet)
                                                 (tImpl 
                                                 (tRel 0) 
                                                 (tSort sSet))])
                                                 (tApp
                                                 (tLambda 
                                                 (nNamed "A") 
                                                 (tSort sSet)
                                                 (tImpl 
                                                 (tRel 0) 
                                                 (tSort sSet)))
                                                 [
                                                 tApp 
                                                 (tRel 1) 
                                                 [tproj1 (tRel 0)]]));
                                                 tInd (mkInd "Top.list" 0);
                                                 tRel 3])) 
                                                 [tproj1 (tRel 1)])
                                                (tApp
                                                 (tproj1
                                                 (tApp
                                                 (tConstruct
                                                 (mkInd
                                                 "Template.sigma.sigma" 0) 0)
                                                 [
                                                 tProd 
                                                 (nNamed "A") 
                                                 (tSort sSet) 
                                                 (tSort sSet);
                                                 tLambda 
                                                 (nNamed "f")
                                                 (tProd 
                                                 (nNamed "A") 
                                                 (tSort sSet) 
                                                 (tSort sSet))
                                                 (tProd 
                                                 (nNamed "A")
                                                 (tApp 
                                                 tΣ
                                                 [
                                                 tSort sSet;
                                                 tLambda 
                                                 (nNamed "A") 
                                                 (tSort sSet)
                                                 (tImpl 
                                                 (tRel 0) 
                                                 (tSort sSet))])
                                                 (tApp
                                                 (tLambda 
                                                 (nNamed "A") 
                                                 (tSort sSet)
                                                 (tImpl 
                                                 (tRel 0) 
                                                 (tSort sSet)))
                                                 [
                                                 tApp 
                                                 (tRel 1) 
                                                 [tproj1 (tRel 0)]]));
                                                 tInd (mkInd "Top.list" 0);
                                                 tRel 4])) 
                                                 [tproj1 (tRel 2)])))
                                          (tImpl
                                             (tApp 
                                                tΣ
                                                [tproj1 (tRel 1);
                                                tProj
                                                 (
                                                 mkInd
                                                 "Template.sigma.sigma" 0,
                                                 2, 1) 
                                                 (tRel 1)])
                                             (tApp
                                                (tLambda 
                                                 (nNamed "f")
                                                 (tImpl
                                                 (tApp
                                                 (tproj1
                                                 (tApp
                                                 (tConstruct
                                                 (mkInd
                                                 "Template.sigma.sigma" 0) 0)
                                                 [
                                                 tProd 
                                                 (nNamed "A") 
                                                 (tSort sSet) 
                                                 (tSort sSet);
                                                 tLambda 
                                                 (nNamed "f")
                                                 (tProd 
                                                 (nNamed "A") 
                                                 (tSort sSet) 
                                                 (tSort sSet))
                                                 (tProd 
                                                 (nNamed "A")
                                                 (tApp 
                                                 tΣ
                                                 [
                                                 tSort sSet;
                                                 tLambda 
                                                 (nNamed "A") 
                                                 (tSort sSet)
                                                 (tImpl 
                                                 (tRel 0) 
                                                 (tSort sSet))])
                                                 (tApp
                                                 (tLambda 
                                                 (nNamed "A") 
                                                 (tSort sSet)
                                                 (tImpl 
                                                 (tRel 0) 
                                                 (tSort sSet)))
                                                 [
                                                 tApp 
                                                 (tRel 1) 
                                                 [tproj1 (tRel 0)]]));
                                                 tInd (mkInd "Top.list" 0);
                                                 tRel 4])) 
                                                 [tproj1 (tRel 2)])
                                                 (tApp
                                                 (tproj1
                                                 (tApp
                                                 (tConstruct
                                                 (mkInd
                                                 "Template.sigma.sigma" 0) 0)
                                                 [
                                                 tProd 
                                                 (nNamed "A") 
                                                 (tSort sSet) 
                                                 (tSort sSet);
                                                 tLambda 
                                                 (nNamed "f")
                                                 (tProd 
                                                 (nNamed "A") 
                                                 (tSort sSet) 
                                                 (tSort sSet))
                                                 (tProd 
                                                 (nNamed "A")
                                                 (tApp 
                                                 tΣ
                                                 [
                                                 tSort sSet;
                                                 tLambda 
                                                 (nNamed "A") 
                                                 (tSort sSet)
                                                 (tImpl 
                                                 (tRel 0) 
                                                 (tSort sSet))])
                                                 (tApp
                                                 (tLambda 
                                                 (nNamed "A") 
                                                 (tSort sSet)
                                                 (tImpl 
                                                 (tRel 0) 
                                                 (tSort sSet)))
                                                 [
                                                 tApp 
                                                 (tRel 1) 
                                                 [tproj1 (tRel 0)]]));
                                                 tInd (mkInd "Top.list" 0);
                                                 tRel 5])) 
                                                 [tproj1 (tRel 3)]))
                                                 (tImpl
                                                 (tApp 
                                                 tΣ
                                                 [
                                                 tApp
                                                 (tproj1
                                                 (tApp
                                                 (tConstruct
                                                 (mkInd
                                                 "Template.sigma.sigma" 0) 0)
                                                 [
                                                 tProd 
                                                 (nNamed "A") 
                                                 (tSort sSet) 
                                                 (tSort sSet);
                                                 tLambda 
                                                 (nNamed "f")
                                                 (tProd 
                                                 (nNamed "A") 
                                                 (tSort sSet) 
                                                 (tSort sSet))
                                                 (tProd 
                                                 (nNamed "A")
                                                 (tApp 
                                                 tΣ
                                                 [
                                                 tSort sSet;
                                                 tLambda 
                                                 (nNamed "A") 
                                                 (tSort sSet)
                                                 (tImpl 
                                                 (tRel 0) 
                                                 (tSort sSet))])
                                                 (tApp
                                                 (tLambda 
                                                 (nNamed "A") 
                                                 (tSort sSet)
                                                 (tImpl 
                                                 (tRel 0) 
                                                 (tSort sSet)))
                                                 [
                                                 tApp 
                                                 (tRel 1) 
                                                 [tproj1 (tRel 0)]]));
                                                 tInd (mkInd "Top.list" 0);
                                                 tRel 5])) 
                                                 [tproj1 (tRel 3)];
                                                 tApp
                                                 (tProj
                                                 (
                                                 mkInd
                                                 "Template.sigma.sigma" 0,
                                                 2, 1)
                                                 (tApp
                                                 (tConstruct
                                                 (mkInd
                                                 "Template.sigma.sigma" 0) 0)
                                                 [
                                                 tProd 
                                                 (nNamed "A") 
                                                 (tSort sSet) 
                                                 (tSort sSet);
                                                 tLambda 
                                                 (nNamed "f")
                                                 (tProd 
                                                 (nNamed "A") 
                                                 (tSort sSet) 
                                                 (tSort sSet))
                                                 (tProd 
                                                 (nNamed "A")
                                                 (tApp 
                                                 tΣ
                                                 [
                                                 tSort sSet;
                                                 tLambda 
                                                 (nNamed "A") 
                                                 (tSort sSet)
                                                 (tImpl 
                                                 (tRel 0) 
                                                 (tSort sSet))])
                                                 (tApp
                                                 (tLambda 
                                                 (nNamed "A") 
                                                 (tSort sSet)
                                                 (tImpl 
                                                 (tRel 0) 
                                                 (tSort sSet)))
                                                 [
                                                 tApp 
                                                 (tRel 1) 
                                                 [tproj1 (tRel 0)]]));
                                                 tInd (mkInd "Top.list" 0);
                                                 tRel 5])) 
                                                 [tRel 3]])
                                                 (tApp
                                                 (tApp
                                                 (tProj
                                                 (
                                                 mkInd
                                                 "Template.sigma.sigma" 0,
                                                 2, 1)
                                                 (tApp
                                                 (tConstruct
                                                 (mkInd
                                                 "Template.sigma.sigma" 0) 0)
                                                 [
                                                 tProd 
                                                 (nNamed "A") 
                                                 (tSort sSet) 
                                                 (tSort sSet);
                                                 tLambda 
                                                 (nNamed "f")
                                                 (tProd 
                                                 (nNamed "A") 
                                                 (tSort sSet) 
                                                 (tSort sSet))
                                                 (tProd 
                                                 (nNamed "A")
                                                 (tApp 
                                                 tΣ
                                                 [
                                                 tSort sSet;
                                                 tLambda 
                                                 (nNamed "A") 
                                                 (tSort sSet)
                                                 (tImpl 
                                                 (tRel 0) 
                                                 (tSort sSet))])
                                                 (tApp
                                                 (tLambda 
                                                 (nNamed "A") 
                                                 (tSort sSet)
                                                 (tImpl 
                                                 (tRel 0) 
                                                 (tSort sSet)))
                                                 [
                                                 tApp 
                                                 (tRel 1) 
                                                 [tproj1 (tRel 0)]]));
                                                 tInd (mkInd "Top.list" 0);
                                                 tRel 6])) 
                                                 [tRel 4])
                                                 [
                                                 tApp 
                                                 (tRel 1) 
                                                 [tproj1 (tRel 0)]])))
                                                [tApp 
                                                 (tRel 1) 
                                                 [tproj1 (tRel 0)]])))
                                       [tApp
                                          (tConstruct (mkInd "Top.list" 0) 1)
                                          [tproj1 (tRel 0)]]] |}];
mind_entry_polymorphic := false;
mind_entry_private := None |}.

Make Inductive list_entryT'.


Definition tsl_one_decl (Σ : global_context) (E : tsl_context)
           (i : inductive) (ind : inductive_body)
  : inductive_body * tsl_context.
  refine (let tsl_ty' := fun t => match tsl_typ Σ E t with
                               | Success _ t => t
                               | Error _ _ => todo_coq
                               end in _).
  refine (let tsl_rec2' := fun t => match tsl_rec2 fuel Σ E [] t with
                                 | Success _ t => t
                                 | Error _ _ => todo_coq
                                 end in _).
  destruct ind. pose (i' := tsl_inductive i). split.
  - econstructor.
    + exact (tsl_ident ind_name).
    + refine (let (nAs, u) := decompose_prod ind_type in
              let (ns, As) := nAs in _).
      refine (let As' := List.map tsl_ty' As in _).
      refine (recompose_prod (ns ++ [nAnon]) (As' ++ [_]) u).
      refine (tApp (tInd i) _).
      refine (from_n (fun n => proj1 (tRel n)) (List.length As)).
    + assumption.
    + refine (List.map tsl_ctor ind_ctors).
    + exact []. (* todo projs *)
  - refine (_ (* ind  *):: _ (* ctors *) ++ _ (* projs *))%list.
    + refine (IndRef i, _).
      exact (pair ind_type (tsl_rec2' ind_type)
                  (tInd i) (tInd i')).
    + refine (map_i _ ind_ctors).
      intros k [[_ typ] _]. refine (ConstructRef i k, _).
      refine (pair _ _ (tConstruct i k) (tConstruct i' k)).
      all: exact todo_coq. (* TODO *)
    + exact []. (* todo projs *)
Defined.

Definition tsl_mind_decl  (Σ : global_context) (E : tsl_context)
           (name : ident) (decl : minductive_decl)
  : global_context * tsl_context.
  unshelve refine (let w : list inductive_body * tsl_context := _
                   in (_, snd w)).
  refine (fold_left_i _ decl.(ind_bodies) ([], [])).
  refine (fun x n ind => let y := tsl_one_entry Σ E (mkInd name n) ind
                      in (fst y :: fst x, snd y ++ snd x)).
  refine [InductiveDecl (tsl_ident name) _]. econstructor.
  exact decl.(ind_npars). exact (fst w).
Defined.



  
Class TranslationInductive :=
  { tsl_ind : mutual_inductive_entry -> global_context * tsl_context }.



Notation "'TYPE'" := (exists A, A -> Type).
Notation "'El' A" := (sigma (π1 A) (π2 A)) (at level 20).

Definition Type_cst := Type.
Translate Type_cst as Typeᶠ.

(* Definition Typeᶠ : El Typeᶠ := *)
(*   @mk_sig Type (fun A => A -> Type) Type (fun A => A -> Type). *)

Check Typeᶠ : El Typeᶠ.

Inductive natR : nat -> Set :=
| OR : natR O
| SR : forall n, natR n -> natR (S n).

Implement Existing nat. exists nat. exact natR. Defined.

Implement Existing bool. exists bool. intro; exact unit. Defined.
Implement to : nat -> bool. cbn -[natᵗ boolᵗ].
Abort.

Definition mkTYPE (A₀ : Type) (Aᴿ : A₀ -> Type) : El Typeᶠ :=
  @mk_sig Type (fun A₀ => A₀ -> Type) A₀ Aᴿ.

Inductive sigmaR (A : TYPE) (B : exists f : A.1 -> Type, forall x : El A, f x.1 -> Type)
  : (exists y, B.1 y) -> Type :=
| mk_sigR : forall (π1 : El A) (π2 : exists y, B.2 π1 y), sigmaR A B (π1.1; π2.1).

Implement Existing sigma. exists sigma. exact sigmaR. Defined.


Inductive eq2 (A : El Typeᶠ) (x : El A) :
  forall (y : El A), eq (π1 x) (π1 y) -> Prop :=
| refl2 : eq2 A x x eq_refl.

Implement Existing eq. cbn.
exists @eq. exact eq2.
Defined.

Quote Recursively Definition eq2_prog := @eq2.
Definition eq2_decl := Eval compute in
      extract_mind_decl_from_program "Top.eq2" eq2_prog.

Compute (option_map (tsl_mind [] [] "Coq.Init.Logic.eq") eq_decl).

Definition eqt_decl := (option_map (tsl_mind [] [] "Coq.Init.Logic.eq") eq_decl).

Compute eqt_decl.

Goal option_map (fun d => ([InductiveDecl "Top.eqᵗ" d], [])) eq2_decl = eqt_decl.
  compute.
Abort.


Implement Existing mk_sig. cbn.
exists @mk_sig. exact mk_sigR.
Defined.

Require Import List.


Inductive listR (A : TYPE) : list A.1 -> Type :=
| nilR : listR A nil
| consR : forall (x : A.1) (l : list A.1), listR A l -> listR A (cons x l).

Implement Existing list. exists list. exact listR. Defined.

Definition T := forall A B, list A -> list B.
Translate T.
Compute (El Tᵗ).

Lemma parametric_map_preserve_length (f : El Tᵗ)
  : forall A B (l : list A), length (f.1 A B l) = length l.
  compute in f.




Definition equiv (A B : Type) :=
  exists (f : A -> B) (g : B -> A), (forall x, g (f x) = x) × (forall y, f (g y) = y).
Translate equiv.

Implement Existing False.
exact (False; fun _ => False).
Defined.

Definition not A := A -> False.
Translate not.

Implement t : forall X, X -> X. cbn.
Abort.

(* Definition hasTwoElements A *)
(*   := exists x y, @eq A x y -> False. *)
(* Translate hasTwoElements. *)

(* Definition HasTwoElFstComponentᶠ : El (Typeᶠ →ᶠ Typeᶠ) := *)
(*   λᶠ (T : El Typeᶠ), mkTYPE (exists (x y : T.1), x = y -> False) (fun _ => unit). *)
(* Definition s := sigma. *)
(* Translate s. *)
Implement notUnivalence : 
  exists A B : Type, (equiv A B) × exists P, P A × not (P B).
Proof. unshelve eapply mk_sigᵗ.  cbn.
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