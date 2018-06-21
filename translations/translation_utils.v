Require Import Template.All.
Require Import List.
Import ListNotations MonadNotation String.
Open Scope string_scope.

Axiom todo : forall {A}, A.


Definition tsl_table := list (global_reference * term).

Fixpoint lookup_tsl_table (E : tsl_table) (gr : global_reference)
  : option term :=
  match E with
  | nil => None
  | hd :: tl =>
    if gref_eq_dec gr (fst hd) then Some (snd hd)
    else lookup_tsl_table tl gr
  end.


Definition tsl_context := (global_context * tsl_table)%type.

Definition emptyTC : tsl_context := (([], uGraph.init_graph), []).

Inductive tsl_error :=
| NotEnoughFuel
| TranslationNotFound (id : ident)
| TranslationNotHandeled
| TypingError (t : type_error).

Inductive tsl_result A :=
| Success : A -> tsl_result A
| Error : tsl_error -> tsl_result A.

Arguments Success {_} _.
Arguments Error {_} _.

Instance tsl_monad : Monad tsl_result :=
  {| ret A a := Success a ;
     bind A B m f :=
       match m with
       | Success a => f a
       | Error e => Error e
       end
  |}.

Instance monad_exc : MonadExc tsl_error tsl_result :=
  { raise A e := Error e;
    catch A m f :=
      match m with
      | Success a => m
      | Error t => f t
      end
  }.



Class Translation := { tsl_id : ident -> ident ;
                       tsl_tm : tsl_context -> term -> tsl_result term ;
                       tsl_ty : tsl_context -> term -> tsl_result term ;
                       tsl_ind : tsl_context -> kername -> kername -> mutual_inductive_body
                            -> tsl_result (tsl_table * list mutual_inductive_body)
                     }.


Definition tsl_ident (id : ident) : ident := (id ++ "ᵗ")%string.

Definition tsl_name tsl_ident n :=
  match n with
  | nAnon => nAnon
  | nNamed n => nNamed (tsl_ident n)
  end.



Definition tTranslate {tsl : Translation} (ΣE : tsl_context) (id : ident)
  : TemplateMonad tsl_context :=
  gr <- tmAbout id ;;
  id' <- tmEval all (tsl_id id) ;;
  mp <- tmCurrentModPath tt ;;
  kn' <- tmEval all (mp ++ "." ++ id') ;;
  match gr with
  | None => fail_nf (id ++ " not found")
  | Some (ConstructRef (mkInd kn n) _)
  | Some (IndRef (mkInd kn n)) =>
      d <- tmQuoteInductive id ;;
      d' <- tmEval lazy (tsl_ind ΣE kn kn' d) ;;
      match d' with
      | Error e => print_nf e ;; fail_nf ("Translation error during the translation of the inductive " ++ id)
      | Success (E, decls) =>
        monad_fold_left (fun _ e => tmMkInductive' e) decls tt ;;
        let Σ' := add_global_decl (InductiveDecl kn d) (fst ΣE) in
        let E' := (E ++ (snd ΣE))%list in
        Σ' <- tmEval lazy Σ' ;;
        E' <- tmEval lazy E' ;;
        print_nf  (kn ++ " has been translated as " ++ id') ;;
        ret (Σ', E')
      end

  | Some (ConstRef kn) =>
    e <- tmQuoteConstant kn true ;;
    match e with
    | ParameterEntry _ => fail_nf (id ++ "is an axiom, not a definition")
    | DefinitionEntry {| definition_entry_type := A;
                         definition_entry_universes := univs;
                         definition_entry_body := t |} =>
      t' <- tmEval lazy (tsl_tm ΣE t) ;;
      match t' with
      | Error e => print_nf e ;; fail_nf ("Translation error during the translation of the body of " ++ id)
      | Success t' =>
        tmMkDefinition id' t' ;;
        let decl := {| cst_universes := univs;
                       cst_type := A; cst_body := Some t |} in
        let Σ' := add_global_decl (ConstantDecl kn decl) (fst ΣE) in
        let E' := (ConstRef kn, tConst kn' []) :: (snd ΣE) in
        Σ' <- tmEval lazy Σ' ;;
        E' <- tmEval lazy E' ;;
        print_nf  (id ++ " has been translated as " ++ id') ;;
        ret (Σ', E')
      end
    end
  end.



Definition tImplement {tsl : Translation} (ΣE : tsl_context)
           (id : ident) (A : Type)
  : TemplateMonad (tsl_context) :=
  tA <- tmQuote A ;;
  tA' <- tmEval lazy (tsl_ty ΣE tA) ;;
  print_nf tA' ;;
  match tA' with
  | Error e => print_nf e ;; fail_nf ("Translation error during the translation of the type of " ++ id)
  | Success tA' =>
      id' <- tmEval all (tsl_id id) ;;
      A' <- tmUnquoteTyped Type tA' ;;
      tmLemma id' A' ;;
      tmAxiom id A ;;
      gr <- tmAbout id ;;
      match gr with
      | Some (ConstRef kn) =>
        let decl := {| cst_universes := Monomorphic_ctx UContext.empty;
                       cst_type := tA; cst_body := None |} in
        let Σ' := add_global_decl (ConstantDecl kn decl) (fst ΣE) in
        let E' := (ConstRef kn, tConst id' []) :: (snd ΣE) in
        print_nf (id ++ " has been translated as " ++ id') ;;
        ret (Σ', E')
      | _ => fail_nf (id ++ " was not found or is not a constant, this is a bug")
      end
  end.

Definition body_constant_entry (e : constant_entry) : option term :=
  match e with
  | ParameterEntry _ => None
  | DefinitionEntry {| definition_entry_body := t |} => Some t
  end.


Definition tmDebug {A} : A -> TemplateMonad unit
  (* := tmPrint. *)
  := fun _ => ret tt.

Definition tImplementExisting {tsl : Translation} (ΣE : tsl_context) (id : ident)
  : TemplateMonad tsl_context :=
  gr <- tmAbout id ;;
  id' <- tmEval all (tsl_id id) ;;
  mp <- tmCurrentModPath tt ;;
  kn' <- tmEval all (mp ++ "." ++ id') ;;
  match gr with
  | None => fail_nf (id ++ " not found")
  | Some (ConstRef kn) =>
    e <- tmQuoteConstant kn true ;;
    match e with
    | ParameterEntry  {| parameter_entry_type := A  |}
    | DefinitionEntry {| definition_entry_type := A |} =>
      tmDebug "plop1" ;;
      ΣE <- tmEval lazy ΣE ;;
      tmDebug ΣE ;;
      tA' <- tmEval lazy (tsl_ty ΣE A) ;;  (* long *)
      tmDebug "plop" ;;
      match tA' with
      | Error e => print_nf e ;; fail_nf ("Translation error during the translation of the type of " ++ id)
      | Success tA' =>
      tmDebug "plop2" ;;
        id' <- tmEval all (tsl_id id) ;;
        A' <- tmUnquoteTyped Type tA' ;;
      tmDebug "plop3" ;;
        tmLemma id' A' ;;
        let decl := {| cst_universes := Monomorphic_ctx UContext.empty;
                       cst_type := A; cst_body := body_constant_entry e |} in
        let Σ' := add_global_decl (ConstantDecl kn decl) (fst ΣE) in
        let E' := (ConstRef kn, tConst id' []) :: (snd ΣE) in
        print_nf (id ++ " has been translated as " ++ id') ;;
        ret (Σ', E')
      end
    end
  | Some (IndRef (mkInd kn n)) =>
    d <- tmQuoteInductive kn ;;
    match List.nth_error (ind_bodies d) n with
      | None => tmFail "bug"
      | Some {| ind_type := A |} => 
      tA' <- tmEval lazy (tsl_ty ΣE A) ;;
      match tA' with
      | Error e => print_nf e ;; fail_nf ("Translation error during the translation of the type of " ++ id)
      | Success tA' =>
        id' <- tmEval all (tsl_id id) ;;
        A' <- tmUnquoteTyped Type tA' ;;
        tmLemma id' A' ;;
        let Σ' := add_global_decl (InductiveDecl kn d) (fst ΣE) in
        let E' := (IndRef (mkInd kn n), tConst id' []) :: (snd ΣE) in
        print_nf (id ++ " has been translated as " ++ id') ;;
        ret (Σ', E')
      end
      (* d' <- tmEval lazy (tsl_ind ΣE kn kn' d) ;; *)
      (* match d' with *)
      (* | Error e => print_nf e ;; fail_nf ("Translation error during the translation of the inductive " ++ id) *)
      (* | Success (E, decls) => *)
      (*   monad_fold_left (fun _ e => tmMkInductive' e) decls tt ;; *)
      (*   let Σ' := add_global_decl (InductiveDecl kn d) (fst ΣE) in *)
      (*   let E' := (E ++ (snd ΣE))%list in *)
      (*   Σ' <- tmEval lazy Σ' ;; *)
      (*   E' <- tmEval lazy E' ;; *)
      (*   print_nf  (kn ++ " has been translated as " ++ id') ;; *)
      (*   ret (Σ', E') *)
    end

  | Some (ConstructRef (mkInd kn n) k) =>
    d <- tmQuoteInductive kn ;;
      tmDebug "plop1" ;;
    match List.nth_error (ind_bodies d) n with
      | None => tmFail "bug"
      | Some {| ind_ctors := ctors |} => 
      tmDebug "plop2" ;;
        match List.nth_error ctors k with
        | None => tmFail "bug'"
        | Some (id, ty, _) =>
      tmDebug "plop3" ;;
          let A := substl (inds kn [] (* FIXME uctx *) (ind_bodies d)) ty in
      tmDebug "plop4" ;;
          tA' <- tmEval lazy (tsl_ty ΣE A) ;;
      tmDebug "plop5" ;;
          match tA' with
          | Error e => print_nf e ;;
                      fail_nf ("Translation error during the translation of the type of " ++ id)
          | Success tA' =>
      tmDebug "plop6" ;;
            id' <- tmEval all (tsl_id id) ;;
            A' <- tmUnquoteTyped Type tA' ;;
      tmDebug "plop7" ;;
            tmLemma id' A' ;;
            let E' := (ConstructRef (mkInd kn n) k, tConst id' []) :: (snd ΣE) in
            print_nf (id ++ " has been translated as " ++ id') ;;
            ret (fst ΣE, E')
          end
        end
    end
  end.



Require Import Ascii.

Fixpoint string_of_ascii_list l :=
  match l with
  | nil => EmptyString
  | a :: s => String a (string_of_ascii_list s)
  end.

Definition string_of_ascii_list_rev l := string_of_ascii_list (rev l).

(* Compute (string_of_ascii_list_rev ["."; "g"; "h"]%char). *)


(* empty list on empty string ?? *)
(* acc is in reverse order *)
Fixpoint split_string_aux (sep : ascii) (s : string) (acc : list ascii)
  : list string :=
  match s with
  | EmptyString => [string_of_ascii_list_rev acc]
  | String a s => if Ascii.ascii_dec a sep then (string_of_ascii_list_rev acc)
                                                 :: (split_string_aux sep s [])
                 else split_string_aux sep s (a :: acc)
  end.

Definition split_string (sep : Ascii.ascii) (s : string) : list string :=
  split_string_aux sep s [].

(* Compute (split_string "."%char "eopjqd.qS.E"). *)
(* Compute (split_string "."%char ""). *)




Definition tTranslateRec {tsl : Translation} (ΣE : tsl_context) {A} (t : A)
  := 
      (* gr <- tmAbout id ;; *)
      (* t <- match gr with *)
      (*     | Some (ConstRef kn) => *)
      (*       tmUnquote (tConst kn []) *)
      (*     | Some (IndRef ind) => *)
      (*       tmUnquote (tInd ind []) *)
      (*     | Some (ConstructRef ind n) => *)
      (*       tmUnquote (tConstruct ind n []) *)
      (*     | None  => fail_nf (id ++ " was not found") *)
      (*     end ;; *)
      (* t' <- tmEval hnf (my_projT2 t) ;; *)
      (* (* let t' := my_projT2 t in *) *)
      (* tmPrint t';; *)
      p <- tmQuoteRec t ;;
      (* tmPrint p ;; *)
      tmPrint "~~~~~~~~~~~~~~~~~~" ;;
      monad_fold_left (
        fun ΣE decl => print_nf ("Translating " ++ global_decl_ident decl) ;;
                             (* print_nf ΣE ;; *)
                    match decl with
                    | ConstantDecl kn decl =>
                      match lookup_tsl_table (snd ΣE) (ConstRef kn) with
                      | Some _ => print_nf (kn ++ " was already translated") ;; ret ΣE
                      | None => 
                        match decl with
                        | {| cst_type := A; cst_body := None; cst_universes := univs |}
                          => fail_nf (kn ++ " is an axiom")
                        
                        | {| cst_type := A; cst_body := Some t; cst_universes := univs |} =>
                          (* tmPrint "go";; *)
                          t' <- tmEval lazy (tsl_tm ΣE t) ;;
                          (* tmPrint "done";; *)
                          match t' with
                          | Error e => print_nf e ;; fail_nf ("Translation error during the translation of the body of " ++ kn)
                          | Success t' =>
                            let id := last (split_string "."%char kn) kn in
                            let id' := tsl_ident id in
                            tmMkDefinition id' t' ;;
                            let Σ' := add_global_decl (ConstantDecl kn decl) (fst ΣE) in
                            let E' := (ConstRef kn, tConst id' []) :: (snd ΣE) in
                            Σ' <- tmEval lazy Σ' ;;
                            E' <- tmEval lazy E' ;;
                            print_nf  (id ++ " has been translated as " ++ id') ;;
                            ret (Σ', E')
                           end
                        end
                      end

                    | InductiveDecl kn d => 
                      match lookup_tsl_table (snd ΣE) (IndRef (mkInd kn 0)) with
                      | Some _ => ret ΣE
                      | None => 
                        let id := last (split_string "."%char kn) kn in
                        let id' := tsl_ident id in
                        let kn' := tsl_ident kn in
                        (* tmPrint "go'";; *)
                        d' <- tmEval lazy (tsl_ind ΣE kn id' d) ;;
                        (* tmPrint "done'";; *)
                        match d' with
                        | Error e => 
                          print_nf e ;; fail_nf ("Translation error during the translation of the inductive " ++ kn)
                        | Success (E, decls) =>
                          monad_fold_left (fun _ e => tmMkInductive' e) decls tt ;;
                                          let Σ' := add_global_decl (InductiveDecl kn d) (fst ΣE) in
                                          let E' := (E ++ (snd ΣE))%list in
                                          Σ' <- tmEval lazy Σ' ;;
                                          E' <- tmEval lazy E' ;;
                                          print_nf  (kn ++ " has been translated as " ++ id') ;;
                                          ret (Σ', E')
                        end
                      end
                    end
      ) (fst p) ΣE
.
