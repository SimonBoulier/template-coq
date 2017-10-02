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

(** Utilities *)

let translate_name id =
  let id = Id.to_string id in
  Id.of_string (id ^ "ᵗ" )

(** Record of translation between globals *)

(* let translator : MTranslate.translator ref = *)
(*   Summary.ref ~name:"Translation Global Table" Refmap.empty *)

(* type translator_obj = (global_reference * global_reference) list *)

(* let add_translator translator l = *)
(*   List.fold_left (fun accu (src, dst) -> Refmap.add src dst accu) translator l *)

(* let cache_translator (_, l) = *)
(*   translator := add_translator !translator l *)

(* let load_translator _ l = cache_translator l *)
(* let open_translator _ l = cache_translator l *)
(* let subst_translator (subst, l) = *)
(*   let map (src, dst) = (subst_global_reference subst src, subst_global_reference subst dst) in *)
(*   List.map map l *)

(* let in_translator : translator_obj -> obj = *)
(*   declare_object { (default_object "TRANSLATOR") with *)
(*     cache_function = cache_translator; *)
(*     load_function = load_translator; *)
(*     open_function = open_translator; *)
(*     discharge_function = (fun (_, o) -> Some o); *)
(*     classify_function = (fun o -> Substitute o); *)
(*   } *)

let global_ctx : Typing0.global_context ref = ref []
let tsl_ctx : Trad.tsl_context ref = ref []

let string_of_global_decl = function
  | Ast0.ConstantDecl (i, _) -> MTranslate.string_of_chars i
  | Ast0.InductiveDecl (i, _) -> MTranslate.string_of_chars i

let string_of_global_ctx g =
  let s = ref "[" in
  List.iter (fun x -> s := !s ^ (string_of_global_decl x) ^ "; ") g;
  !s ^ "]"

let string_of_tsl_ctx g =
  let s = ref "[" in
  List.iter (fun (x, y) -> s := !s ^ "(" ^ (MTranslate.string_of_chars x) ^ "," ^ (MTranslate.string_of_chars y) ^ "); ") g;
  !s ^ "]"

let string_of_array pr a =
  let s = ref "[|" in
  Array.iter (fun x -> s := !s ^ (pr x) ^ "; ") a;
  !s ^ "|]"


let rec dump r =
  if Obj.is_int r then
    string_of_int (Obj.magic r : int)
  else (* Block. *)
    let rec get_fields acc = function
      | 0 -> acc
      | n -> let n = n-1 in get_fields (Obj.field r n :: acc) n
    in
    let rec is_list r =
      if Obj.is_int r then
        r = Obj.repr 0 (* [] *)
      else
        let s = Obj.size r and t = Obj.tag r in
        t = 0 && s = 2 && is_list (Obj.field r 1) (* h :: t *)
    in
    let rec get_list r =
      if Obj.is_int r then
        []
      else
        let h = Obj.field r 0 and t = get_list (Obj.field r 1) in
        h :: t
    in
    let opaque name =
      (* XXX In future, print the address of value 'r'.  Not possible
       * in pure OCaml at the moment.  *)
      "<" ^ name ^ ">"
    in
    let s = Obj.size r and t = Obj.tag r in
    (* From the tag, determine the type of block. *)
    match t with
    | _ when is_list r ->
      let fields = get_list r in
      "[" ^ String.concat "; " (List.map dump fields) ^ "]"
    | 0 ->
      let fields = get_fields [] s in
      "(" ^ String.concat ", " (List.map dump fields) ^ ")"
    | x when x = Obj.lazy_tag ->
      (* Note that [lazy_tag .. forward_tag] are < no_scan_tag.  Not
         * clear if very large constructed values could have the same
         * tag. XXX *)
      opaque "lazy"
    | x when x = Obj.closure_tag ->
      opaque "closure"
    | x when x = Obj.object_tag ->
      let fields = get_fields [] s in
      let _clasz, id, slots =
        match fields with
        | h::h'::t -> h, h', t
        | _ -> assert false
      in
      (* No information on decoding the class (first field).  So just print
         * out the ID and the slots. *)
      "Object #" ^ dump id ^ " (" ^ String.concat ", " (List.map dump slots) ^ ")"
    | x when x = Obj.infix_tag ->
      opaque "infix"
    | x when x = Obj.forward_tag ->
      opaque "forward"
    | x when x < Obj.no_scan_tag ->
      let fields = get_fields [] s in
      "Tag" ^ string_of_int t ^
      " (" ^ String.concat ", " (List.map dump fields) ^ ")"
    | x when x = Obj.string_tag ->
      "\"" ^ String.escaped (Obj.magic r : string) ^ "\""
    | x when x = Obj.double_tag ->
      string_of_float (Obj.magic r : float)
    | x when x = Obj.abstract_tag ->
      opaque "abstract"
    | x when x = Obj.custom_tag ->
      opaque "custom"
    | x when x = Obj.final_tag ->
      opaque "final"
    | x when x = Obj.double_array_tag ->
       string_of_array string_of_float (Obj.magic r : float array)
    | _ ->
      opaque (Printf.sprintf "unknown: tag %d size %d" t s)

let dump v = dump (Obj.repr v)




open Entries

let translate_constr ?types env sigma c id =
  let (body, sigma) = MTranslate.translate env !global_ctx !tsl_ctx sigma c in
  (* Feedback.msg_debug (str"evar"); *)
  (* let evdref = ref sigma in *)
  (* let body = Typing.e_solve_evars env evdref body in *)
  (* let sigma = !evdref in *)
  (* Feedback.msg_debug (str"evar done"); *)
  (* Feedback.msg_debug (str ("dump: " ^ (dump body))); *)
  (* let (sigma, t) = Typing.type_of env sigma body in *)
  Feedback.msg_debug (str "type:" ++ Printer.pr_constr_env env sigma c);
  Feedback.msg_debug (str "type:" ++ Printer.pr_constr_env env sigma body);
  let (_, uctx) = Evd.universe_context sigma in
  let ce   = Declare.definition_entry ?types ~univs:uctx body in
  let cd   = Entries.DefinitionEntry ce in
  (* let t = ce.const_entry_body in *)
  let decl = (cd, IsProof Theorem) in
  Feedback.msg_debug (str"Declaring constant " ++ (Id.print id));
  (* Feedback.msg_debug (str ("dump: " ^ (dump decl))); *)
  let cst_ = Declare.declare_constant id decl in
  Feedback.msg_debug (str "Declared");
  body, ConstRef cst_



let translate gr id' =
  Feedback.msg_debug(str"Translate " ++ Libnames.pr_reference gr);
  Feedback.msg_debug (str ("global env: " ^ (string_of_global_ctx !global_ctx)));
  Feedback.msg_debug (str ("tsl env: " ^ (string_of_tsl_ctx !tsl_ctx)));
  let gr = Nametab.global gr in
  (* Feedback.msg_debug (str "full_path:" ++ Libnames.pr_path (Nametab.path_of_global gr)); *)
  let quoted_id  = MTranslate.chars_of_string (Libnames.string_of_path (Nametab.path_of_global gr)) in
  let id' = match id' with
    | Some id -> id
    | None -> translate_name (Nametab.basename_of_global gr)
  in
  (* Feedback.msg_debug (str "full_path:" ++ Libnames.pr_path (Lib.make_path id')); *)
  let quoted_id' = MTranslate.chars_of_string (Libnames.string_of_path (Lib.make_path id')) in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let typ = Universes.unsafe_type_of_global gr in
  let typ', sigma = MTranslate.translate_type env !global_ctx !tsl_ctx sigma typ in
  let end_with () =
    tsl_ctx := (quoted_id, quoted_id') :: !tsl_ctx;
    Feedback.msg_info (str"Global " ++ Printer.pr_global gr ++ str" has been translated as " ++ Names.Id.print id' ++ str".") in
  match gr with
  | ConstRef cst ->
     let body = match Global.body_of_constant cst with
       | Some body -> body
       | _ -> CErrors.anomaly (Pp.str "Are you trying to translate some axiom?") in
     let decl = Ast0.{ cst_name = quoted_id; cst_type = Template_coq.quote_term env typ;
                       cst_body = Some (Template_coq.quote_term env body) (* TODO not unquote twice *) } in
     global_ctx := (Ast0.ConstantDecl (quoted_id, decl)) :: !global_ctx;
     let _ = translate_constr ~types:typ' env sigma body id' in end_with ()
  (* let quoted_id' = MTranslate.chars_of_string (Libnames.string_of_path (Nametab.path_of_global gr')) in *)
  (* tsl_ctx := (quoted_id, quoted_id') :: !tsl_ctx; *)
  | IndRef ind ->
     global_ctx := (Template_coq.quote_mind_decl env (fst ind)) :: !global_ctx;
     let kind = Global, Flags.use_polymorphic_flag (), DefinitionBody Definition in
     Feedback.msg_debug (str "typ:" ++ Printer.pr_constr_env env sigma typ);
     Feedback.msg_debug (str "typ':" ++ Printer.pr_constr_env env sigma typ');
     Feedback.msg_debug (str "evarmap:" ++ Evd.pr_evar_map None sigma);
     Lemmas.start_proof id' kind sigma typ' (Lemmas.mk_hook (fun _ _ -> end_with ()))
  | ConstructRef c ->
     let kind = Global, Flags.use_polymorphic_flag (), DefinitionBody Definition in
     Lemmas.start_proof id' kind sigma typ' (Lemmas.mk_hook (fun _ _ -> end_with ()))
  (* translate_constr env sigma (mkConstruct c) id' *)
  (* Est-ce qu'il faut ajouter au global ctx ? *)
  | _ -> error "Translation not handled."


                    
let implement id typ idopt =
  Feedback.msg_debug(str"Implement " ++ Names.Id.print id);
  Feedback.msg_debug (str ("global env: " ^ (string_of_global_ctx !global_ctx)));
  Feedback.msg_debug (str ("tsl env: " ^ (string_of_tsl_ctx !tsl_ctx)));
  let id_ = match idopt with
    | Some id' -> id'
    | None -> translate_name id
  in
  let env = Global.env () in
  let typ, uctx = Constrintern.interp_type env (Evd.from_env env) typ in
  let sigma = Evd.from_ctx uctx in
  (* let evdref = ref (Evd.from_env env) in *)
  (* let typ = Constrintern.interp_type_evars env evdref typ in *)
  (* let sigma = !evdref in *)
  Feedback.msg_debug (str "typ:" ++ Printer.pr_constr_env env sigma typ);
  Feedback.msg_debug (str "evarmap:" ++ Evd.pr_evar_map ~with_univs:true None sigma);
  let typ_, sigma = MTranslate.translate_type env !global_ctx !tsl_ctx sigma typ in
  Feedback.msg_debug (str "typ':" ++ Printer.pr_constr_env env sigma typ_);
  Feedback.msg_debug (str "evarmap:" ++ Evd.pr_evar_map None sigma);
  (* let (sigma, _) = Typing.type_of env sigma typ_ in *)
  (* Feedback.msg_debug (str"pp"); *)
  (* Feedback.msg_debug (Evd.pr_evar_map ~with_univs:true None sigma); *)
  let hook _ dst =
    (** Declare the original term as an axiom *)
    let param = (None, false, (typ, UState.context (Evd.evar_universe_context sigma)), None) in
    let cb = Entries.ParameterEntry param in
    let cst = Declare.declare_constant id (cb, IsDefinition Definition) in
    (** Attach the axiom to the implementation *)
    (* Feedback.msg_debug (str "full_path:" ++ Libnames.pr_path (Lib.make_path id)); *)
    (* Feedback.msg_debug (str "full_path:" ++ Libnames.pr_path (Lib.make_path id_)); *)
    let quoted_ident  = MTranslate.chars_of_string (Libnames.string_of_path (Lib.make_path id)) in
    let quoted_ident' = MTranslate.chars_of_string (Libnames.string_of_path (Lib.make_path id_)) in
    tsl_ctx := (quoted_ident, quoted_ident' ) :: !tsl_ctx;
  in
  let hook ctx = Lemmas.mk_hook hook in
  (* let sigma, _ = Typing.type_of env sigma typ_ in *)
  let kind = Global, Flags.use_polymorphic_flag (), DefinitionBody Definition in
  Lemmas.start_proof_univs id_ kind sigma typ_ hook


(** Error handling *)

let _ = register_handler
	begin function
	(* | MTranslate.MissingGlobal gr -> *)
	(*    let ref = Nametab.shortest_qualid_of_global Id.Set.empty gr in *)
	(*    str "No translation for global " ++ Libnames.pr_qualid ref ++ str "." *)
	| _ -> raise Unhandled
end
