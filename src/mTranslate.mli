open Globnames

val string_of_chars : char list -> string
val chars_of_string : string -> char list

val translate : Environ.env -> Typing0.global_context -> Trad.tsl_context -> Evd.evar_map -> Constr.t -> Constr.t * Evd.evar_map

val translate_type : Environ.env -> Typing0.global_context -> Trad.tsl_context -> Evd.evar_map -> Constr.t -> Constr.t * Evd.evar_map
