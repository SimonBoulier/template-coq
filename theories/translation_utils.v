Require Import Template.Ast Template.Typing Template.Checker.
Require Import List.
Import ListNotations.


Definition tsl_context := list (ident * ident).

Fixpoint lookup_tsl_ctx (E : tsl_context) (id : ident) : option ident :=
  match E with
  | nil => None
  | hd :: tl =>
    if ident_eq id (fst hd) then Some (snd hd)
    else lookup_tsl_ctx tl id
  end.


Section MonadMap.
  Import MonadNotation.
  Context {T} {M : Monad T}.

  Fixpoint monad_map {A} {B} (f : A -> T B) (l : list A) : T (list B)
    := match l with
       | nil => ret nil
       | x :: l => x' <- f x ;;
                  l' <- monad_map f l ;;
                  ret (x' :: l')
       end.
End MonadMap.


Inductive tsl_error :=
| NotEnoughFuel : tsl_error
| TranslationNotFound : ident -> tsl_error
| TranslationNotHandeled
| TypingError.

Inductive tsl_result A :=
| Success : A -> tsl_result A
| Error : tsl_error -> tsl_result A.

Instance tsl_monad : Monad tsl_result :=
  {| ret A a := Success A a ;
     bind A B m f :=
       match m with
       | Success _ a => f a
       | Error _ e => Error _ e
       end
  |}.

Instance monad_exc : MonadExc tsl_error tsl_result :=
  { raise A e := Error A e;
    catch A m f :=
      match m with
      | Success _ a => m
      | Error _ t => f t
      end
  }.


Require Import Template.Template Template.sigma.

Quote Definition tSigma := sigma.
Quote Definition tPair := @mk_sig.
Definition pair (typ1 typ2 t1 t2 : term) : term
  := tApp tPair [ typ1 ; typ2 ; t1 ; t2].
Definition pack (t u : term) : term
  := tApp tSigma [ t ; u ].
Definition proj1 (t : term) : term
  := tProj (mkInd "Template.sigma.sigma" 0, 2, 0) t.
Definition proj2 (t : term) : term
  := tProj (mkInd "Template.sigma.sigma" 0, 2, 1) t.
Definition proj (b : bool) (t : term) : term
  := tProj (mkInd "Template.sigma.sigma" 0, 2, if b then 0 else 1) t.

Quote Definition tBool := bool.
Quote Definition tTrue := true.
Definition timesBool (t : term) :=
  tApp tSigma [t; tLambda nAnon t tBool].
Definition pairTrue typ t := pair typ tBool t tTrue.