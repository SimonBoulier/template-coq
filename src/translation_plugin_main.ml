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
open Unquote
open Tsl_fun

(** Utilities *)

let translate_name id =
  let id = Id.to_string id in
  Id.of_string (id ^ "ᵗ" )

(** Record of translation between globals *)

let global_ctx : Typing0.global_context ref = ref []
let tsl_ctx : Translation_utils.tsl_context ref = ref []

let add_global_ctx x =
  global_ctx := x :: !global_ctx

let add_tsl_ctx x =
  tsl_ctx := x :: !tsl_ctx

let string_of_global_decl = function
  | Ast0.ConstantDecl (i, _) -> string_of_chars i
  | Ast0.InductiveDecl (i, _) -> string_of_chars i

let string_of_global_ctx g =
  let s = ref "[" in
  List.iter (fun x -> s := !s ^ (string_of_global_decl x) ^ "; ") g;
  !s ^ "]"

let string_of_tsl_ctx (g:Translation_utils.tsl_context) =
  let s = ref "[" in
  List.iter (fun (x, y) -> s := !s ^ "(" ^ (string_of_chars (Translation_utils.string_of_gref x)) ^ "," ^ (Unquote.string_of_term y) ^ "); ") g;
  !s ^ "]"

let string_of_array pr a =
  let s = ref "[|" in
  Array.iter (fun x -> s := !s ^ (pr x) ^ "; ") a;
  !s ^ "|]"


let string_of_error = function
  | Translation_utils.NotEnoughFuel -> "Not enough fuel"
  | Translation_utils.TranslationNotFound t -> "Translation of " ^ string_of_chars t ^ " not found"
  | Translation_utils.TranslationNotHandeled -> "Translation not handeled"
  | Translation_utils.TypingError -> "Typing error"

let wrap_extracted_function f =
  fun env global_ctx tsl_ctx sigma c ->
  let c = Template_coq.quote_term env c in
  let c = f global_ctx tsl_ctx c in
  let c = match c with
    | Translation_utils.Success x -> x
    | Translation_utils.Error e -> error ("Translation raised an error: " ^ string_of_error e) in
  unquote sigma c

let translate = wrap_extracted_function tsl
let translate_type = wrap_extracted_function tsl_type



let quote_gr : global_reference -> Translation_utils.global_reference = function
  | VarRef _ -> failwith "Quoting of variables not handeled"
  | ConstRef c -> Translation_utils.ConstRef (Template_coq.quote_string (Names.Constant.to_string c))
  | IndRef (i, n) -> Translation_utils.IndRef (Ast0.Coq_mkInd (Template_coq.quote_string (Names.string_of_kn (Names.canonical_mind i)), Template_coq.quote_int n))
  | ConstructRef ((i,n),k) -> Translation_utils.ConstructRef ((Ast0.Coq_mkInd (Template_coq.quote_string (Names.string_of_kn (Names.canonical_mind i)), Template_coq.quote_int n)), Template_coq.quote_int k)



type translation_operation = Translate of global_reference | ImplementExisting of global_reference | Implement of Constrexpr.constr_expr

let translate_implement op (id : Names.Id.t) id' =
  let s = match op with
    | Translate _ -> "Translate "
    | ImplementExisting _ -> "Implement Existing "
    | Implement _ -> "Implement " in
  Feedback.msg_debug(str s ++ Ppconstr.pr_id id);
  Feedback.msg_debug (str ("global env: " ^ (string_of_global_ctx !global_ctx)));
  Feedback.msg_debug (str ("tsl env: " ^ (string_of_tsl_ctx !tsl_ctx)));
  let quoted_id  = Template_coq.quote_ident id in
  let id' = match id' with
    | Some id -> id
    | None -> translate_name id
  in
  let quoted_id' = chars_of_string (Libnames.string_of_path (Lib.make_path id')) in
  let env   = Global.env () in
  let sigma = Evd.from_env env in
  let sigma, typ = match op with
    | Translate gr | ImplementExisting gr -> sigma, Universes.unsafe_type_of_global gr
    | Implement ce -> let typ, uctx = Constrintern.interp_type env (Evd.from_env env) ce in
                      Evd.from_ctx uctx, typ in
  let sigma, typ' = translate_type env !global_ctx !tsl_ctx sigma typ in
  let kind = Global, Flags.use_polymorphic_flag (), DefinitionBody Definition in
  let end_with hook decl =
    let gr = hook () in
    Option.iter add_global_ctx decl;
    add_tsl_ctx (gr, Ast0.Coq_tConst quoted_id');
    Feedback.msg_info (Ppconstr.pr_id id ++ str" has been translated as " ++ Names.Id.print id' ++ str".") in
  match op with
  | Translate gr ->
     (match gr with
      | ConstRef cst ->
         (match Global.body_of_constant cst with
          | Some body -> let (sigma, body) = translate env !global_ctx !tsl_ctx sigma body in
                         (* let evdref = ref sigma in *)
                         (* let body = Typing.e_solve_evars env evdref body in *)
                         (* let sigma = !evdref in *)
                         (* let (sigma, t) = Typing.type_of env sigma body in *)
                         let (_, uctx) = Evd.universe_context sigma in
                         let ce = Declare.definition_entry ~types:typ' ~univs:uctx body in
                         let cd = Entries.DefinitionEntry ce in
                         let decl = (cd, IsProof Theorem) in
                         let _ = Declare.declare_constant id' decl in
                         let decl = Ast0.{ cst_name = quoted_id; cst_type = Template_coq.quote_term env typ;
                                           cst_body = Some (Template_coq.quote_term env body) (* TODO not unquote twice *) } in
                         end_with (fun () -> quote_gr gr) (Some (Ast0.ConstantDecl (quoted_id, decl)))
          | _ -> error "Please use 'Implement Existing' to translate an axioms.")
      | IndRef ind ->
         error "Please use 'Implement Existing' to translate inductive types."
      | ConstructRef c ->
         error "Please use 'Implement Existing' to translate constructors."
      | VarRef _ -> error "Translation not handled.")
  | ImplementExisting gr ->
     let decl = match gr with
       | ConstRef cst ->
          (match Global.body_of_constant cst with
           | Some body -> error "Please use 'Translate' to translate definitions."
           | None -> let decl = Ast0.{ cst_name = quoted_id; cst_type = Template_coq.quote_term env typ;
                                       cst_body = None } in
                     Some (Ast0.ConstantDecl (quoted_id, decl)))
       | IndRef (ind, _) -> Some (Template_coq.quote_mind_decl env ind)
       | ConstructRef c -> None
       | VarRef _ -> error "Translation of variables not handled." in
     Lemmas.start_proof id' kind sigma typ' (Lemmas.mk_hook (fun _ _ -> end_with (fun () -> quote_gr gr) decl))
  | Implement _ ->
     let hook () =
       (** Declare the original term as an axiom *)
       let param = (None, false, (typ, UState.context (Evd.evar_universe_context sigma)), None) in
       let cb = Entries.ParameterEntry param in
       let cst = Declare.declare_constant id (cb, IsDefinition Definition) in
       Translation_utils.ConstRef (Template_coq.quote_string (Names.Constant.to_string cst)) in
     Lemmas.start_proof id' kind sigma typ' (Lemmas.mk_hook (fun _ _ -> end_with hook None))


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
