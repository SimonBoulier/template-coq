open Constrarg
open Extraargs
open Translation_plugin_main

DECLARE PLUGIN "translation"



VERNAC COMMAND EXTEND TransTranslation CLASSIFIED AS SIDEFF
| [ "Translate" global(gr) ] -> [ translate gr None ]
| [ "Translate" global(gr) "as" ident(id) ] -> [ translate gr (Some id) ]
END


let classify_impl _ = Vernacexpr.(VtStartProof ("Classic",Doesn'tGuaranteeOpacity,[]), VtLater)

VERNAC COMMAND EXTEND TransImplementation CLASSIFIED BY classify_impl
| [ "Implement" ident(id) ":" lconstr(typ) ] -> [ implement id typ None ]
| [ "Implement" ident(id) ":" lconstr(typ) "as" ident(id') ] -> [ implement id typ (Some id') ]
END

VERNAC COMMAND EXTEND TransImplementationEx CLASSIFIED BY classify_impl
| [ "Implement" "Existing" global(gr) ] -> [ implement_existing gr None ]
| [ "Implement" "Existing" global(gr) "as" ident(id') ] -> [ implement_existing gr (Some id') ]
END
