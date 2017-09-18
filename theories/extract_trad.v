(** Extraction setup for template-coq.
    
    Any extracted code planning to link with the plugin's OCaml reifier
    should use these same directives for consistency.
*)

Require Import Template.trad.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

Extraction Blacklist Ast String List Nat Typing.

Extraction Library trad.