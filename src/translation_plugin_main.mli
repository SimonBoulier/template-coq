
val translate : Libnames.reference -> Names.Id.t option -> unit

val implement_existing : Libnames.reference -> Names.Id.t option -> unit

val implement : Names.Id.t -> Constrexpr.constr_expr -> Names.Id.t option -> unit
