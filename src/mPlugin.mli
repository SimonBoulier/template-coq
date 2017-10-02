open Names
open Libnames
open Proofview

val translate : reference -> Id.t option -> unit

val implement : Id.t -> Constrexpr.constr_expr -> Id.t option -> unit

val implement_existing : reference -> Id.t option -> unit
