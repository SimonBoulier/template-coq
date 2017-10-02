(** Translate from Coq terms to Template_AST terms *)
val quote_int : int -> Datatypes.nat
val quote_ident : Names.Id.t -> char list
val quote_string : string -> char list
(* val quote_inductive : char list * Datatypes.nat -> Ast0.inductive *)
val quote_mind_decl : Environ.env -> Names.mutual_inductive -> Ast0.global_decl
val quote_term : Environ.env -> Constr.t -> Ast0.term
val quote_term_rec : Environ.env -> Constr.t -> Ast0.program
