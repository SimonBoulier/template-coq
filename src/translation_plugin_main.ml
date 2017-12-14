open CErrors
open Pp
open Util
open Names
open Context
open Term
open Decl_kinds
open Libobject
open Globnames
open Proofview.Notations
open Entries
(* open Unquote *)
open Reify.TemplateCoqQuoter
open Reify.TermReify
(** Utilities *)

open Feedback

let debug n = Feedback.msg_debug (int n)
       
let translate_name id =
  let id = Id.to_string id in
  Id.of_string (id ^ "ᵗ" )

(** Record of translation between globals *)

let pkg_tsl = ["Template";"tsl_param"]
let pkg_ast = ["Template";"Ast"]
let pkg_tsl_utils = ["Template";"translation_utils"]
let pkg_datatypes = ["Coq";"Init";"Datatypes"]

(* let tsl_path = *)
  (* DirPath.make (List.map Id.of_string ["tsl_fun"; "Template"]) *)
(* let make_kn name = *)
  (* KerName.make2 (MPfile tsl_path) (Label.make name) *)
(* let tsl = Constant.make1 (make_kn "tsl") *)

let rsu = resolve_symbol pkg_tsl_utils
let rsa = resolve_symbol pkg_ast
let rsdt = resolve_symbol pkg_datatypes
                        
let global_ctx : Term.constr ref = ref (resolve_symbol pkg_tsl_utils "empty_global_ctx")
let tsl_ctx : Term.constr ref = ref (resolve_symbol pkg_tsl_utils "empty_tsl_ctx")

let quote_gr = function
  | VarRef _ -> failwith "var"
  | ConstRef cst -> Term.mkApp (rsu "ConstRef", [|quote_kn (Names.Constant.canonical cst)|])
  | IndRef ind -> Term.mkApp (rsu "IndRef", [|quote_inductive2 ind |])
  | ConstructRef (ind, n) -> Term.mkApp (rsu "ConstructRef", [|quote_inductive2 ind; int_to_nat n |])
                      
let add_tsl_ctx env gr tm =
  tsl_ctx := Term.mkApp (rsu "add_tsl_ctx", [|quote_gr gr; quote_term env tm; !tsl_ctx|])

let quote_option env (t : Term.constr option) : Term.constr (* de type Option term *) =
  match t with
  | Some t -> Term.mkApp (rsdt "Some", [|rsa "term"; quote_term env t|])
  | None -> rsdt "None"

let quote_constant_decl env cst : Term.constr (* constant_decl *) =
  let decl = Environ.lookup_constant cst env in
  let id = quote_kn (Names.Constant.canonical cst) in
  let ty = quote_term env (Typeops.type_of_constant_type env decl.Declarations.const_type) in
  let optbody = Declareops.body_of_constant (Environ.opaque_tables env) decl in
  let optbody = quote_option env optbody in
  Term.mkApp (rsa "Build_constant_decl", [|id; ty; optbody|])
                        
(* let quote_inductive_body env (ind : Declarations.one_inductive_body) : Term.constr (\* inductive_body *\) = *)
(*   let open Declarations in *)
(*   let name = ind in *)
(*   let typ = k in *)
(*   let kelim = l in *)
(*   let ctors = l in *)
(*   let projs = l in *)
(*   Term.mkApp (rsa "mkinductive_body", [|name; typ; kelim; ctors; projs|]) *)

(* let quote_mind_decl2 env mind : Term.constr (\* minductive_decl *\) = *)
(*   let open Declarations in *)
(*   let decl = Environ.lookup_mind mind env in *)
(*   let npars = int_to_nat decl.mind_nparams in *)
(*   let bodies = to_coq_list (rsa "term") (List.map (quote_inductive_body env) (Array.to_list decl.mind_packets)) in *)
(*   Term.mkApp (rsa "Build_minductive_decl", [|npars; bodies|]) *)

let quote_mind_decl2 env mind : Term.constr (* minductive_decl *) =
  let t = quote_mind_decl env mind in
  debug 21;
  msg_debug (Printer.pr_constr t);
  let (h,args) = Term.destApp t in
  if Term.eq_constr h (rsa "PType") then
    match args with
    | [| _ ; npars ; bodies|] ->
       Term.mkApp (rsa "Build_minductive_decl", [|npars; bodies|])
    | _ -> failwith "bad term (more applied?)"
  else
    failwith "strange quote_mind_decl2"

let quote_gr_decl env (gr:global_reference) =
  match gr with
  | VarRef _ -> failwith "var"
  | ConstRef cst -> Some (Term.mkApp (rsa "ConstantDecl", [|quote_kn (Names.Constant.canonical cst); quote_constant_decl env cst|]))
  | IndRef (mind,0) -> Some (Term.mkApp (rsa "InductiveDecl", [|quote_kn (Names.MutInd.canonical mind); quote_mind_decl2 env mind|]))
  (* | IndRef _ -> None *)
  (* | ConstructRef _ -> None *)
  | _ -> None
           
let add_global_ctx env gr  =
  Option.iter (fun decl' -> global_ctx := Term.mkApp (rsu "add_global_ctx", [|decl'; !global_ctx|]))
              (quote_gr_decl env gr)

let from_tsl_result trm =
  (* let (h,args) = app_full trm [] in *)
  let (h,args) = Term.destApp trm in
  if Term.eq_constr h (rsu "Success") then
    match args with
    | [| _ ; x |] -> x
    | _ -> failwith "bad term"
  else if Term.eq_constr h (rsu "Error") then
    failwith "tsl_error"
  else
    failwith "strange"


let wrap_tsl_function f env sigma typ =
  let typ = Reify.TermReify.quote_term env typ in
  (* debug 10; *)
  let tc = Term.mkApp (f, [|!global_ctx; !tsl_ctx; typ|]) in
  debug 11; msg_debug (Printer.pr_constr tc);
  let t = Reductionops.nf_all env sigma tc in
  let t = from_tsl_result t in
  (* msg_debug (Printer.pr_constr t); *)
  let sigmaref = ref sigma in
  let t = Reify.Denote.denote_term sigmaref t in
  (* debug 13; *)
  msg_debug (str "tsl type/tm: " ++ Printer.pr_constr t);
  (!sigmaref, t)

(* let tsl = resolve_symbol pkg_tsl "tsl" *)
(* let tsl_type = resolve_symbol pkg_tsl "tsl_type" *)
                      
let translate =
  let env = Global.env () in
  debug 7;
  let (_, tsl) = Typeclasses.resolve_one_typeclass env (Evd.from_env env) (rsu "Translation") in (* unsafe *)
  (* let p = rsu "tsl_tm" in *)
  (* msg_debug (Printer.pr_constr p);   *)
  (* let tsl = mkProj (p,tsl) in *)
  wrap_tsl_function (Term.mkApp (rsu "tsl_tm", [|tsl|]))
                    
let translate_type =
  let env = Global.env () in
  let (_, tsl) = Typeclasses.resolve_one_typeclass env (Evd.from_env env) (rsu "TranslationType") in (* unsafe *)
  let t = (Term.mkApp (rsu "tsl_typ", [|tsl|])) in
  msg_debug (Printer.pr_constr t);
  wrap_tsl_function t

type translation_operation = Translate of global_reference | ImplementExisting of global_reference | Implement of Constrexpr.constr_expr

let translate_implement op (id : Names.Id.t) id' =
  let s = match op with
    | Translate _ -> "Translate "
    | ImplementExisting _ -> "Implement Existing "
    | Implement _ -> "Implement " in
  Feedback.msg_debug(str s ++ Ppconstr.pr_id id);
  Feedback.msg_debug (str "global env:" ++ Printer.pr_constr !global_ctx);
  Feedback.msg_debug (str "tsl env: " ++ Printer.pr_constr !tsl_ctx);
  let id' = match id' with
    | Some id -> id
    | None -> translate_name id
  in
  let env   = Global.env () in
  let sigma = Evd.from_env env in
  let sigma, typ =
    match op with
    | Translate gr | ImplementExisting gr ->
       sigma, Universes.unsafe_type_of_global gr
    | Implement ce ->
       let typ, uctx = Constrintern.interp_type env (Evd.from_env env) ce in
       Evd.from_ctx uctx, typ in
  let sigma, typ' = translate_type env sigma typ in
  let kind = Global, Flags.use_polymorphic_flag (), DefinitionBody Definition in
  let end_with hook tm' =
    let gr = hook () in
    let env = Global.env () in
    add_global_ctx env gr;
    add_tsl_ctx env gr tm';
    Feedback.msg_info (Ppconstr.pr_id id ++ str" has been translated as " ++ Names.Id.print id' ++ str".") in
  match op with
  | Translate gr ->
     (match gr with
      | ConstRef cst ->
         (match Global.body_of_constant cst with
          | Some body ->
                         (* debug 1; msg_debug (Printer.pr_constr body); *)
                         let (sigma, body) = translate env sigma body in debug 2;
                         (* let evdref = ref sigma in *)
                         (* let body = Typing.e_solve_evars env evdref body in *)
                         (* let sigma = !evdref in *)
                         (* let (sigma, t) = Typing.type_of env sigma body in *)
                         let (_, uctx) = Evd.universe_context sigma in
                         let ce = Declare.definition_entry ~types:typ' ~univs:uctx body in
                         let cd = Entries.DefinitionEntry ce in
                         let decl = (cd, IsProof Theorem) in
                         let tm' = Declare.declare_constant id' decl in
                         end_with (fun () -> gr) (Term.mkConst tm')
          | _ -> error "Please use 'Implement Existing' to translate an axioms.")
      | IndRef ind ->
         error "Please use 'Implement Existing' to translate inductive types."
      | ConstructRef c ->
         error "Please use 'Implement Existing' to translate constructors."
      | VarRef _ -> error "Translation of variables not handled.")
  | ImplementExisting gr ->
     (match gr with
      | ConstRef cst ->
         (match Global.body_of_constant cst with
          | Some _ -> error "Please use 'Translate' to translate definitions."
          | None -> ())
      | IndRef (ind, _) -> ()
      | ConstructRef c -> ()
      | VarRef _ -> error "Translation of variables not handled.");
       Lemmas.start_proof id' kind sigma typ' (Lemmas.mk_hook (fun _ gr' -> end_with (fun () -> gr) (Term.mkConst (Globnames.destConstRef gr'))))
  | Implement _ ->
     let hook () =
       (** Declare the original term as an axiom *)
       let param = (None, false, (typ, UState.context (Evd.evar_universe_context sigma)), None) in
       let cb = Entries.ParameterEntry param in
       let cst = Declare.declare_constant id (cb, IsDefinition Definition) in
       ConstRef cst
     in
     Lemmas.start_proof id' kind sigma typ' (Lemmas.mk_hook (fun _ gr' -> end_with hook (Term.mkConst (Globnames.destConstRef gr'))))


let translate (gr:Libnames.reference) = let gr = Nametab.global gr in translate_implement (Translate gr) (Nametab.basename_of_global gr)
let implement_existing (gr:Libnames.reference) = let gr = Nametab.global gr in translate_implement (ImplementExisting gr) (Nametab.basename_of_global gr)
let implement (id:Names.Id.t) typ = translate_implement (Implement typ) id















  (* let gr = Nametab.global gr in *)
  (* Feedback.msg_debug (str "full_path:" ++ Libnames.pr_path (Nametab.path_of_global gr)); *)
(* (Nametab.basename_of_global gr) *)
  (* Feedback.msg_debug (str "full_path:" ++ Libnames.pr_path (Lib.make_path id')); *)


(* let implement id typ idopt = *)
(*   Feedback.msg_debug(str"Implement " ++ Names.Id.print id); *)
(*   Feedback.msg_debug (str ("global env: " ^ (string_of_global_ctx !global_ctx))); *)
(*   Feedback.msg_debug (str ("tsl env: " ^ (string_of_tsl_ctx !tsl_ctx))); *)
(*   let id_ = match idopt with *)
(*     | Some id' -> id' *)
(*     | None -> translate_name id *)
(*   in *)
(*   (\* let evdref = ref (Evd.from_env env) in *\) *)
(*   (\* let typ = Constrintern.interp_type_evars env evdref typ in *\) *)
(*   (\* let sigma = !evdref in *\) *)
(*   Feedback.msg_debug (str "typ:" ++ Printer.pr_constr_env env sigma typ); *)
(*   Feedback.msg_debug (str "evarmap:" ++ Evd.pr_evar_map ~with_univs:true None sigma); *)
(*   let typ_, sigma = translate_type env !global_ctx !tsl_ctx sigma typ in *)
(*   Feedback.msg_debug (str "typ':" ++ Printer.pr_constr_env env sigma typ_); *)
(*   Feedback.msg_debug (str "evarmap:" ++ Evd.pr_evar_map None sigma); *)
(*   (\* let (sigma, _) = Typing.type_of env sigma typ_ in *\) *)
(*   (\* Feedback.msg_debug (str"pp"); *\) *)
(*   (\* Feedback.msg_debug (Evd.pr_evar_map ~with_univs:true None sigma); *\) *)
(*   let hook _ dst = *)
(*     (\** Declare the original term as an axiom *\) *)
(*     let param = (None, false, (typ, UState.context (Evd.evar_universe_context sigma)), None) in *)
(*     let cb = Entries.ParameterEntry param in *)
(*     let cst = Declare.declare_constant id (cb, IsDefinition Definition) in *)
(*     (\** Attach the axiom to the implementation *\) *)
(*     (\* Feedback.msg_debug (str "full_path:" ++ Libnames.pr_path (Lib.make_path id)); *\) *)
(*     (\* Feedback.msg_debug (str "full_path:" ++ Libnames.pr_path (Lib.make_path id_)); *\) *)
(*     let quoted_ident  = chars_of_string (Libnames.string_of_path (Lib.make_path id)) in *)
(*     let quoted_ident' = chars_of_string (Libnames.string_of_path (Lib.make_path id_)) in *)
(*     tsl_ctx := (quoted_ident, quoted_ident' ) :: !tsl_ctx; *)
(*   in *)
(*   let hook ctx = Lemmas.mk_hook hook in *)
(*   (\* let sigma, _ = Typing.type_of env sigma typ_ in *\) *)
(*   let kind = Global, Flags.use_polymorphic_flag (), DefinitionBody Definition in *)
(*   Lemmas.start_proof_univs id_ kind sigma typ_ hook *)


(* (\** Error handling *\) *)

(* let _ = register_handler *)
(* 	begin function *)
(* 	(\* | MissingGlobal gr -> *\) *)
(* 	(\*    let ref = Nametab.shortest_qualid_of_global Id.Set.empty gr in *\) *)
(* 	(\*    str "No translation for global " ++ Libnames.pr_qualid ref ++ str "." *\) *)
(* 	| _ -> raise Unhandled *)
(* end *)
