open Constrarg
open Extraargs

DECLARE PLUGIN "translation"



VERNAC COMMAND EXTEND TransTranslation CLASSIFIED AS SIDEFF
| [ "Translate" global(gr) ] -> [ MPlugin.translate gr None ]
| [ "Translate" global(gr) "as" ident(id) ] -> [ MPlugin.translate gr (Some id) ]
END


let classify_impl _ = Vernacexpr.(VtStartProof ("Classic",Doesn'tGuaranteeOpacity,[]), VtLater)

VERNAC COMMAND EXTEND TransImplementation CLASSIFIED BY classify_impl
| [ "Implement" ident(id) ":" lconstr(typ) ] -> [ MPlugin.implement id typ None ]
| [ "Implement" ident(id) ":" lconstr(typ) "as" ident(id') ] -> [ MPlugin.implement id typ (Some id') ]
END

VERNAC COMMAND EXTEND TransImplementationEx CLASSIFIED BY classify_impl
| [ "Implement" "Existing" global(gr) ] -> [ MPlugin.translate gr None ]
| [ "Implement" "Existing" global(gr) "as" ident(id') ] -> [ MPlugin.translate gr (Some id') ]
END
