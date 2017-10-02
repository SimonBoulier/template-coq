open Constrarg
open Extraargs

DECLARE PLUGIN "translation"


let classify_impl _ = Vernacexpr.(VtStartProof ("Classic",Doesn'tGuaranteeOpacity,[]), VtLater)


(* VERNAC COMMAND EXTEND TransTranslation CLASSIFIED AS SIDEFF *)
VERNAC COMMAND EXTEND TransTranslation CLASSIFIED BY classify_impl
| [ "Translate" global(gr) ] -> [ MPlugin.translate gr None ]
| [ "Translate" global(gr) "as" ident(id) ] -> [ MPlugin.translate gr (Some id) ]
END

VERNAC COMMAND EXTEND TransImplementation CLASSIFIED BY classify_impl
| [ "Implement" ident(id) ":" lconstr(typ) ] -> [ MPlugin.implement id typ None ]
| [ "Implement" ident(id) ":" lconstr(typ) "as" ident(id') ] -> [ MPlugin.implement id typ (Some id') ]
END
