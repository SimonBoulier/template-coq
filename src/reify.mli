module type Quoter = sig
  type t

  type quoted_ident
  type quoted_int
  type quoted_name
  type quoted_sort
  type quoted_cast_kind
  type quoted_kernel_name
  type quoted_inductive
  type quoted_decl
  type quoted_program
  type quoted_proj
  type quoted_sort_family
  open Names

  val quote_ident : Id.t -> quoted_ident
  val quote_name : Name.t -> quoted_name
  val quote_int : int -> quoted_int
  val quote_sort : Sorts.t -> quoted_sort
  val quote_sort_family : Sorts.family -> quoted_sort_family
  val quote_cast_kind : Constr.cast_kind -> quoted_cast_kind
  val quote_kn : kernel_name -> quoted_kernel_name
  val quote_inductive : quoted_kernel_name * quoted_int -> quoted_inductive
  val quote_proj : quoted_inductive -> quoted_int -> quoted_int -> quoted_proj
  val mkName : quoted_ident -> quoted_name
  val mkAnon : quoted_name

  val mkRel : quoted_int -> t
  val mkVar : quoted_ident -> t
  val mkMeta : quoted_int -> t
  val mkEvar : quoted_int -> t array -> t

  val mkSort : quoted_sort -> t
  val mkCast : t -> quoted_cast_kind -> t -> t
  val mkProd : quoted_name -> t -> t -> t
  val mkLambda : quoted_name -> t -> t -> t
  val mkLetIn : quoted_name -> t -> t -> t -> t
  val mkApp : t -> t array -> t
  val mkConst : quoted_kernel_name -> t
  val mkInd : quoted_inductive -> t
  val mkConstruct : quoted_inductive * quoted_int -> t
  val mkCase : (quoted_inductive * quoted_int) -> quoted_int list -> t -> t ->
               t list -> t
  val mkProj : quoted_proj -> t -> t
  val mkFix : (quoted_int array * quoted_int) * (quoted_name array * t array * t array) -> t
  val mkCoFix : quoted_int * (quoted_name array * t array * t array) -> t
    

  val mkMutualInductive : quoted_kernel_name -> quoted_int (* params *) ->
                          (quoted_ident * t (* ind type *) * quoted_sort_family list *
                             (quoted_ident * t (* constr type *) * quoted_int) list *
                               (quoted_ident * t) list (* projections *)) list ->
                          quoted_decl
  val mkConstant : quoted_kernel_name -> t -> t -> quoted_decl
  val mkAxiom : quoted_kernel_name -> t -> quoted_decl

  val mkExt : quoted_decl -> quoted_program -> quoted_program
  val mkIn : t -> quoted_program 
end

module Reify(Q : Quoter) : sig
  val quote_mind_decl : Environ.env -> Names.mutual_inductive -> Q.quoted_decl
  val quote_term : Environ.env -> Constr.t -> Q.t
  val quote_term_rec : Environ.env -> Constr.t -> Q.quoted_program
end
  
val kn_of_canonical_string : string -> Names.kernel_name

module TemplateCoqQuoter : sig
  val resolve_symbol : string list -> string -> Term.constr
  val to_coq_list : Term.constr (* the type *) -> Term.constr list -> Term.constr
  val int_to_nat : int -> Term.constr
  val quote_string : string -> Term.constr
  val quote_kn : Names.kernel_name -> Term.constr
  val quote_inductive2 : Names.inductive -> Term.constr
end
                                         
module TermReify : sig
  val quote_term : Environ.env -> Term.constr -> Term.constr
  val quote_mind_decl : Environ.env -> Names.mutual_inductive -> Term.constr
end

module Denote : sig
  val from_coq_pair : Term.constr -> Term.constr * Term.constr
  val unquote_map_option : (Term.constr -> 'a) -> Term.constr -> 'a option
  val denote_term : Evd.evar_map ref -> Term.constr -> Term.constr
end
