(** Extraction setup for template-coq.
    
    Any extracted code planning to link with the plugin's OCaml reifier
    should use these same directives for consistency.
*)

Require Import Template.translation_utils Template.tsl_param Template.tsl_fun Template.tsl_p.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

Extraction Blacklist Ast String List Nat Typing.

Extraction Library translation_utils.
Extraction Library tsl_param.
Extraction Library tsl_fun.
Extraction Library tsl_p.