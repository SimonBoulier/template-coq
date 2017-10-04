open Globnames

val string_of_chars : char list -> string
val chars_of_string : string -> char list

val unquote : Evd.evar_map -> Ast0.term -> Evd.evar_map * Term.constr
