(* Require Import Template.Template Template.Ast. *)
(* Require Import Template.Induction Template.Typing Template.Checker. *)
(* Import String Lists.List.ListNotations. *)
(* Open Scope list_scope. Open Scope string_scope. *)

(* Reserved Notation "M 'ᵗ'" (at level 20). *)
(* (* Axiom todo : forall {A}, A. *) *)

(* Fixpoint tsl_inductive (t : inductive) : inductive := *)
(*   match t with *)
(*   (* | mkInd : string -> nat -> inductive. *) *)
(*   | mkInd s n => mkInd s n *)
(*   end. *)

(* (* Definition projection : Set := inductive * nat (* params *) * nat (* argument *). *) *)
(* Fixpoint tsl_projection (t : projection) : projection := *)
(*   match t with *)
(*   | (i , n , m) => (tsl_inductive i , n , m) *)
(*   end. *)

(* Set Primitive Projections. *)
(* Record prod' A B : Type := *)
(*   pair' { fst' : A ; snd' : B }. *)
(* Arguments fst' {A B} _. *)
(* Arguments snd' {A B} _. *)

(* Quote Definition tBool := bool. *)
(* Quote Definition tTimes := prod'. *)
(* Definition timesBool (t : term) : term *)
(*   := tApp tTimes [ t ; tBool ]. *)
(* Quote Definition tTrue := true. *)
(* Quote Definition tPair := pair'. *)
(* Definition pairTrue (A t : term) : term *)
(*   := tApp tPair [ A ; tBool ; t ; tTrue]. *)
(* (* Test Quote ((pair' _ _ true 4).(snd')). *) *)
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
(* (* Test Quote (snd' (pair' _ _ true 4)). *) *)
(* Definition fstProj (t : term) : term *)
(*   := tProj (mkInd "Template.trad.prod'" 0, 2, 0) t. *)

(* Definition tsl_context := list (ident * ident). *)

(* Fixpoint lookup_tsl_ctx (E : tsl_context) (id : ident) : option ident := *)
(*   match E with *)
(*   | nil => None *)
(*   | hd :: tl => *)
(*     if ident_eq id (fst hd) then Some (snd hd) *)
(*     else lookup_tsl_ctx tl id *)
(*   end. *)

(* (* Quote Recursively Definition t := bool. *) *)

(* (* Definition initial_context : global_context := *) *)
(* (*   [ InductiveDecl "Coq.Init.Datatypes.bool" 0 *) *)
(* (*                   [{| ind_name := "bool"; *) *)
(* (*                       ind_type := tSort sSet; *) *)
(* (*                       ctors := [("true", tRel 0, 0); ("false", tRel 0, 0)]; *) *)
(* (*                       projs := [] |}] ]. *) *)

(* Fixpoint tsl_rec (Σ : global_context) (E : tsl_context) (Γ : context) (t : term) {struct t} *)
(*   : term := *)
(*   match t with *)
(*   (* | tRel       : nat -> term *) *)
(*   | tRel n => tRel n *)
(*   (* | tVar       : ident -> term (** For free variables (e.g. in a goal) *) *) *)
(*   | tVar v => tVar v *)
(*   (* | tMeta      : nat -> term   (** NOTE: this can go away *) *) *)
(*   | tMeta n => tMeta n *)
(*   (* | tEvar      : nat -> list term -> term *) *)
(*   | tEvar n l => tEvar n (List.map (tsl_rec Σ E Γ) l) *)
(*   (* | tSort      : sort -> term *) *)
(*   | tSort s => tSort s *)
(*   (* | tCast      : term -> cast_kind -> term -> term *) *)
(*   | tCast t c A => tCast (tsl_rec Σ E Γ t) c (tsl_rec Σ E Γ A) *)
(*   (* | tProd      : name -> term (** the type **) -> term -> term *) *)
(*   | tProd n A B => let A' := tsl_rec Σ E Γ A in timesBool (tProd n A' (tsl_rec Σ E (Γ ,, vass n A') B)) *)
(*   (* | tLambda    : name -> term (** the type **) -> term -> term *) *)
(*   | tLambda n A t => let A' := tsl_rec Σ E Γ A in *)
(*                     let t' := tLambda n A' (tsl_rec Σ E (Γ ,, vass n A') t) in *)
(*                     match infer Σ Γ t' with *)
(*                     | Checked A' => pairTrue A' t' *)
(*                     | _ => (* FIXME *) tBool *)
(*                     end *)
(*     (* t' *) *)
(*   (* | tLetIn     : name -> term (** the term **) -> term (** the type **) -> term -> term *) *)
(*   | tLetIn n t A u => let t' := tsl_rec Σ E Γ t in *)
(*                      let A' := tsl_rec Σ E Γ A in *)
(*                      tLetIn n t' A' (tsl_rec Σ E (Γ ,, vdef n t' A') u) *)
(*   (* | tApp       : term -> list term -> term *) *)
(*   | tApp (tInd i) u => tApp (tInd i) (List.map (tsl_rec Σ E Γ) u) *)
(*   | tApp (tConstruct i n) u => tApp (tConstruct i n) (List.map (tsl_rec Σ E Γ) u) *)
(*   | tApp t u => tApp (fstProj (tsl_rec Σ E Γ t)) (List.map (tsl_rec Σ E Γ) u) *)
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
(*   | tCase (i , n) t u l => tCase (tsl_inductive i , n) (tsl_rec Σ E Γ t) (tsl_rec Σ E Γ u) (List.map (fun nt => (fst nt , tsl_rec Σ E Γ (snd nt))) l) *)
(*   (* | tProj      : projection -> term -> term *) *)
(*   | tProj p t => tProj (tsl_projection p) (tsl_rec Σ E Γ t) *)
(*   (* | tFix       : mfixpoint term -> nat -> term *)  (* mfixpoint = list (def term) *) *)
(*   | tFix l n => tFix (List.map (map_def (tsl_rec Σ E Γ)) l) n *)
(*   (* | tCoFix     : mfixpoint term -> nat -> term. *) *)
(*   | tCoFix l n => tCoFix (List.map (map_def (tsl_rec Σ E Γ)) l) n *)
(*   end. *)

(* Definition tsl := tsl_rec. *)
(* Definition tsl_type:= tsl_rec. *)

(* (* Require Import Vector. *) *)
(* (* Quote Recursively Definition t := (fun x : nat => VectorDef.t bool x). *) *)
(* Quote Recursively Definition n := nat. *)
(* Let E := fst (decompose_program n []). *)
(* Eval cbn in E. *)

(* Quote Definition t := (fun x:nat => x). *)
(* Eval cbn in (infer E [] t). *)

(* (* Definition tsl (c : string) (Σ : global_context) (E : tsl_context) (t : term) *) *)
(* (*   : term * global_context * tsl_context *) *)
(* (*   (* := let t' := tsl_rec Σ E [] t in (t' , Σ, (c , t') :: E). *) *) *)
(* (*   := let t' := tsl_rec Σ E [] t in (t' , Σ, (c , t') :: E). *) *)


(* (* Fixpoint tsl_program (p : program) (Σ : global_context) (E : tsl_context term) *) *)
(* (*   : term * tsl_context term *) *)
(* (*   := match p with *) *)
(* (*      | PConstr s t u p => *) *)
(* (*      | PType n k l p => *) *)
(* (*      | PAxiom n t p => *) *)
(* (*      | PIn t => *) *)
(* (*      end. *) *)

           

(* (* Existing Class tsl_context. *) *)
(* (* Instance toto : tsl_context term := []. *) *)

(* (* Axiom M : 0 = 0. *) *)
(* (* Make Definition Mᵗ := ltac:(let a:= type of M in *) *)
(* (*                             let k x:= *) *)
(* (*                                 (let tu := eval compute in (tsl "M" [] x) in *) *)
(* (*                                  let t := eval compute in (fst tu) in *) *)
(* (*                                  let u := eval compute in (snd tu) in *) *)
(* (*                                      (* declare_instance u *) *) *)
(* (*                                      exact t) in *) *)
(* (*                             quote_term a k). *) *)
(* (* Goal Mᵗ. *) *)
(* (*   red. constructor; auto.  *) *)
(* (* Defined. *) *)



(* (* Extraction tsl. *) *)



(* (* Fixpoint tsl (t : S.Term) : T.Term := *) *)
(* (*   match t with *) *)
(* (*   | S.Var v => Var v *) *)
(* (*   | S.Sort s => !s *) *)
(* (*   | S.Π A B => Σ (Π (A ᵗ) (B ᵗ)) Bool *) *)
(* (*   | S.λ A M => ⟨λ (A ᵗ) (M ᵗ), true⟩ *) *)
(* (*   | S.App M N => (π1 (M ᵗ)) · (N ᵗ) *) *)
(* (*   | S.Eq A M N => Eq (A ᵗ) (M ᵗ) (N ᵗ) *) *)
(* (*   | S.refle M => refle (M ᵗ) *) *)
(* (*   | S.J A P t1 u t2 p => J (A ᵗ) (P ᵗ) (t1 ᵗ) (u ᵗ) (t2 ᵗ) (p ᵗ) *) *)
(* (*   end *) *)
(* (* where " M 'ᵗ'" := (tsl M). *) *)













(* <<<>>>> *)





Require Import Template.Template Template.Ast.
Require Import Template.Induction Template.Typing Template.Checker.
Import String Lists.List.ListNotations.
Open Scope list_scope. Open Scope string_scope.

Reserved Notation "M 'ᵗ'" (at level 20).
(* Axiom todo : forall {A}, A. *)


Set Primitive Projections.
Record sigma A B :=
  mk_sig { π1 : A ; π2 : B π1 }.
Arguments π1 {A B} _.
Arguments π2 {A B} _.
Arguments mk_sig {A B} _ _.

Quote Definition tSigma := sigma.
Quote Definition tPair := @mk_sig.
Definition pair (typ1 typ2 t1 t2 : term) : term
  := tApp tPair [ typ1 ; typ2 ; t1 ; t2].
Definition pack (t u : term) : term
  := tApp tSigma [ t ; u ].
(* Test Quote ((pair' _ _ true 4).(snd')). *)
(* Make Definition x := (tProj (mkInd "Top.prod'" 0, 2, 1) *)
(*    (tApp (tConstruct (mkInd "Top.prod'" 0) 0) *)
(*       [tInd (mkInd "Coq.Init.Datatypes.bool" 0); *)
(*       tInd (mkInd "Coq.Init.Datatypes.nat" 0); *)
(*       tConstruct (mkInd "Coq.Init.Datatypes.bool" 0) 0; *)
(*       tApp (tConstruct (mkInd "Coq.Init.Datatypes.nat" 0) 1) *)
(*         [tApp (tConstruct (mkInd "Coq.Init.Datatypes.nat" 0) 1) *)
(*            [tApp (tConstruct (mkInd "Coq.Init.Datatypes.nat" 0) 1) *)
(*               [tApp (tConstruct (mkInd "Coq.Init.Datatypes.nat" 0) 1) *)
(*                  [tConstruct (mkInd "Coq.Init.Datatypes.nat" 0) 0]]]]])). *)
(* Test Quote (snd' (pair' _ _ true 4)). *)
Definition proj1 (t : term) : term
  := tProj (mkInd "Template.trad.sigma" 0, 2, 0) t.
Definition proj2 (t : term) : term
  := tProj (mkInd "Template.trad.sigma" 0, 2, 1) t.
Definition proj (b : bool) (t : term) : term
  := tProj (mkInd "Template.trad.sigma" 0, 2, if b then 0 else 1) t.

Definition tsl_context := list (ident * ident).

Fixpoint lookup_tsl_ctx (E : tsl_context) (id : ident) : option ident :=
  match E with
  | nil => None
  | hd :: tl =>
    if ident_eq id (fst hd) then Some (snd hd)
    else lookup_tsl_ctx tl id
  end.



Quote Definition todo := True.
Reserved Notation "'tsl_typ'".
Reserved Notation "'tsl_term'".

(* if b it is the first translation, else the second *)
Fixpoint tsl_rec (fuel : nat) (Σ : global_context) (E : tsl_context) (Γ : context) (b : bool) (t : term) {struct fuel}
  : term :=
  match fuel with
  | O => todo
  | S fuel =>
  match t with
  (* | tRel       : nat -> term *)
  | tRel n => proj b (tRel n)
  (* | tVar       : ident -> term (** For free variables (e.g. in a goal) *) *)
  | tVar v => proj b (tVar v)
  (* | tMeta      : nat -> term   (** NOTE: this can go away *) *)
  | tMeta n => proj b (tMeta n)
  (* | tEvar      : nat -> list term -> term *)
  | tEvar n l => tEvar n (List.map (tsl_typ fuel Σ E Γ) l)
  (* | tSort      : sort -> term *)
  | tSort s => if b then tSort s
              else tLambda (nNamed "A") (tSort s) (tProd nAnon (tRel 0) (tSort s))
  (* | tCast      : term -> cast_kind -> term -> term *)
  | tCast t c A => if b then tCast (tsl_rec fuel Σ E Γ true t) c (tsl_rec fuel Σ E Γ true A)
                  else tCast (tsl_rec fuel Σ E Γ false t) c (tApp (tsl_rec fuel Σ E Γ false A) [tsl_rec fuel Σ E Γ true t])
  (* | tProd      : name -> term (** the type **) -> term -> term *)
  | tProd n A B => if b then
                    tProd n (tsl_typ fuel Σ E Γ A) (tsl_rec fuel Σ E (Γ ,, vass n A) true B)
                  else
                    let A' := tsl_typ fuel Σ E Γ A in
                    tLambda (nNamed "f") (tProd n A' (tsl_rec fuel Σ E Γ true B))
                            (tProd n A'(tApp (tsl_rec fuel Σ E Γ false B)
                                             [tApp (tRel 1) [tRel 0]]))
  (* | tLambda    : name -> term (** the type **) -> term -> term *)
  | tLambda n A t => let A' := tsl_typ fuel Σ E Γ A in tLambda n A' (tsl_rec fuel Σ E (Γ ,, vass n A') b t)
  (* | tLetIn     : name -> term (** the term **) -> term (** the type **) -> term -> term *)
  | tLetIn n t A u => let t' := tsl_term fuel Σ E Γ t in
                     let A' := tsl_typ fuel Σ E Γ A in
                     tLetIn n t' A' (tsl_rec fuel Σ E (Γ ,, vdef n t' A') b u)
  (* | tApp       : term -> list term -> term *)
  | tApp (tInd i) u => tApp (tInd i) (List.map (tsl_rec fuel Σ E Γ b) u)
  | tApp (tConstruct i n) u => tApp (tConstruct i n) (List.map (tsl_rec fuel Σ E Γ b) u)
  | tApp t u => tApp (tsl_rec fuel Σ E Γ b t) (List.map (tsl_term fuel Σ E Γ) u)
  (* | tConst     : string -> term *)
  | tConst s => match lookup_tsl_ctx E s with
               | Some t => tConst t
               | None => todo
               end
  (* | tInd       : inductive -> term *)
  | tInd (mkInd s _) => match lookup_tsl_ctx E s with
                       | Some t => tConst t
                       | None => todo
                       end
  (* | tConstruct : inductive -> nat -> term *)
  | tConstruct (mkInd s _) n => match lookup_env Σ s with
                               | Some decl => todo
                               | None => todo
                               end
  (* | tCase      : (inductive * nat) (* # of parameters *) -> term (** type info **) -> term -> *)
  (*                list (nat * term) -> term *)
  | tCase (i , n) t u l => todo
  (* | tProj      : projection -> term -> term *)
  | tProj p t => todo
  (* | tFix       : mfixpoint term -> nat -> term *)  (* mfixpoint = list (def term) *)
  | tFix l n => tFix (List.map (map_def (tsl_rec fuel Σ E Γ b)) l) n
  (* | tCoFix     : mfixpoint term -> nat -> term. *)
  | tCoFix l n => tCoFix (List.map (map_def (tsl_rec fuel Σ E Γ b)) l) n
  end
end
where "'tsl_typ'" := (fun fuel Σ E Γ t => pack (tsl_rec fuel Σ E Γ true t) (tsl_rec fuel Σ E Γ false t))
and  "'tsl_term'" := (fun fuel Σ E Γ t => let typ := match infer Σ Γ t with
                                             | Checked A => A
                                             | _ => todo end in
                                  let t1 := tsl_rec fuel Σ E Γ true t in
                                  let t2 := tsl_rec fuel Σ E Γ false t in
                                  let typ1 := tsl_rec fuel Σ E Γ true typ in
                                  let typ2 := tsl_rec fuel Σ E Γ false typ in
                                  pair typ1 typ2 t1 t2).



Definition tsl := tsl_term 1000.
Definition tsl_type:= tsl_typ 1000.

(* Test Quote Type. *)
(* Compute (tsl [] [] [] (tSort (sType BinNums.xH))). *)
(* Make Definition hj := (tApp (tConstruct (mkInd "Top.sigma" 0) 0) *)
(*          [tSort (sType (BinNums.xO 1)); *)
(*          tProd (nNamed "A") (tSort (sType BinNums.xH)) *)
(*            (tSort (sType (BinNums.xO 1))); tSort (sType BinNums.xH); *)
(*          tLambda (nNamed "A") (tSort (sType BinNums.xH)) *)
(*            (tProd nAnon (tRel 0) (tSort (sType BinNums.xH)))]). *)