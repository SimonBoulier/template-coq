open CErrors
open Names
open Term
open Declarations
open Environ
open Globnames
open Pp


let string_of_array pr a =
  let s = ref "[|" in
  Array.iter (fun x -> s := !s ^ (pr x) ^ ";") a;
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






open Ast0
open Pre_env

let todo n = failwith ("todo" ^ (string_of_int n))

(* let quote_decl_cst env (k : Names.Constant.t) (b : constant_body) : Typing0.global_decl = *)
(*   let n : Ast0.ident = Template_coq.quote_string (Names.string_of_con k) in *)
(*   let typ : Ast0.term = Template_coq.quote_term env (Typeops.type_of_constant_type env (Declareops.type_of_constant b)) in *)
(*   let body : Ast0.term = Template_coq.quote_term env (Option.get (Declareops.body_of_constant (opaque_tables env) b)) in *)
(*   Typing0.ConstantDecl (n, typ, body) *)

(* FIXME: mutual *)
(* let quote_decl_ind env (k : Names.MutInd.t) (b : mutual_inductive_body) : Typing0.global_decl = *)
(*   let f (c : one_inductive_body) : Ast0.inductive_body = *)
(*     { ind_name = todo 0; *)
(*       ind_type = todo 1; *)
(*       ctors = todo 2; *)
(*       projs = todo 3; } in *)
(* (\*   ind_name : Ast0.ident; *\) *)
(* (\*   ind_type : Ast0.term; *\) *)
(* (\*   ctors : ((Ast0.ident * Ast0.term) * Datatypes.nat) list; *\) *)
(* (\*   projs : (Ast0.ident * Ast0.term) list; *\) *)
(*   let l : Ast0.inductive_body list = List.map f (Array.to_list b.mind_packets) in *)

(*   let n : Ast0.ident = Template_coq.quote_string (Names.string_of_kn (Names.canonical_mind k)) in *)
(*   let k : Datatypes.nat = Template_coq.quote_int b.mind_ntypes in *)
(*   Typing0.InductiveDecl (n, k, l) *)


(* let quote_ctx (env : Environ.env) : Typing0.global_context * Typing0.context = *)
(*   let globals = (pre_env env).env_globals in *)
(*   let consts, inds = globals.env_constants, globals.env_inductives in *)
(*   let ll = (Cmap_env.bindings consts) in *)
(*   List.iter (fun (s,_) -> Feedback.msg_debug (Names.debug_pr_con s)) ll; *)
(*   (\* let inds = mindmap_env.fold (fun k b l -> (quote_decl_ind env k (fst b)) :: l) inds [] in *\) *)
(*   let inds = [] in *)
(*   let consts_inds = Cmap_env.fold (fun k b l -> (quote_decl_cst env k (fst b)) :: l) consts inds in *)
(*   (consts_inds, []) *)


let rec unquote_nat : Datatypes.nat -> int = function
  | Datatypes.O -> 0
  | Datatypes.S n -> succ (unquote_nat n)

let string_of_chars (l : char list) : string =
  String.init (List.length l) (List.nth l)

let chars_of_string (s : string) =
  Array.to_list (Array.init (String.length s) (String.get s))

let unquote_ident (i : Ast0.ident) : Names.Id.t =
  Names.id_of_string (string_of_chars i)

let unquote_name : Ast0.name -> Names.Name.t = function
  | Coq_nAnon -> Anonymous
  | Coq_nNamed i -> Name (unquote_ident i)

let unquote_sort sigma s =
  match s with
  | Coq_sProp -> sigma, Term.mkProp
  | Coq_sSet -> sigma, Term.mkSet
  | Coq_sType _ -> let sigma, s' = Evd.new_sort_variable Evd.univ_flexible sigma in
                   (* Global.push_context false (snd (Evd.universe_context sigma)); *)
                   sigma, mkSort s'

let unquote_cast = function
  | VmCast -> VMcast
  | NativeCast -> NATIVEcast
  | Cast -> DEFAULTcast
  | RevertCast -> REVERTcast


let sigma_map (f : 's -> 'a -> 's * 'b) (s : 's) (l : 'a list) : 's * ('b list) =
  let s, l' = List.fold_left (fun (s, l) a -> let s'', b = f s a in s'', b :: l) (s, []) l in
  s, List.rev l'


let unquote_inductive (Coq_mkInd (s, n) : Ast0.inductive) =
  Names.mind_of_kn (Reify.kn_of_canonical_string (string_of_chars s)), unquote_nat n


let rec unquote sigma (t : Ast0.term) : Evd.evar_map * Term.constr =
  match t with
  | Coq_tRel n -> sigma, mkRel (unquote_nat n + 1)
  | Coq_tVar s -> sigma, mkVar (unquote_ident s)
  | Coq_tMeta n -> sigma, mkMeta (unquote_nat n)
  | Coq_tEvar (n, l) -> let sigma, l = sigma_map unquote sigma l in sigma, mkEvar (todo 4, Array.of_list l)
  | Coq_tSort s -> unquote_sort sigma s
  | Coq_tCast (t, k, u) ->
     let sigma, t' = unquote sigma t in
     let sigma, u' = unquote sigma u in
     sigma, mkCast (t', unquote_cast k, u')
  | Coq_tProd (n, t, u) ->
     let sigma, t' = unquote sigma t in
     let sigma, u' = unquote sigma u in
     sigma, mkProd (unquote_name n, t', u')
  | Coq_tLambda (n, t, u) ->
     let sigma, t' = unquote sigma t in
     let sigma, u' = unquote sigma u in
     sigma, mkLambda (unquote_name n, t', u')
  | Coq_tLetIn (n, t, u, v) ->
     let sigma, t' = unquote sigma t in
     let sigma, u' = unquote sigma u in
     let sigma, v' = unquote sigma v in
     sigma, mkLetIn (unquote_name n, t', u', v')
  | Coq_tApp (t, l) ->
     let sigma, t' = unquote sigma t in
     let sigma, l = sigma_map unquote sigma l in
     sigma, mkApp (t', Array.of_list l)
  | Coq_tConst s -> sigma, mkConst (Names.constant_of_kn (Reify.kn_of_canonical_string (string_of_chars s)))
  | Coq_tInd ind -> sigma, mkInd (unquote_inductive ind)
  | Coq_tConstruct (ind, k) ->
     sigma, mkConstruct (unquote_inductive ind, unquote_nat k + 1)
  | Coq_tCase (* of (Ast0.inductive * Datatypes.nat) * Ast0.term * Ast0.term * (Datatypes.nat * Ast0.term) list *) _ -> todo 5
  | Coq_tProj (((ind, k), n), t) (* Ast0.projection * Ast0.term *) ->
     let sigma, t' = unquote sigma t in
     let ind' = unquote_inductive ind in
     let (mib,mip) = Global.lookup_inductive ind' in
     let s = match mib.mind_record with
       | Some (Some (id, projs, pbs)) -> projs.(unquote_nat n)
       | _ -> failwith "lkenr" in
     (* let _, ind' = Global.lookup_inductive ind' in *)
     (* Feedback.msg_debug (Names.Id.print ind'.mind_typename ++ int(unquote_nat n)++str" __ "++int (Array.length ind'.mind_consnames)); *)
     (* let i = Inductiveops.get_projections env *)
     (* (\* let s = ind'.mind_consnames.(unquote_nat n) in *\) *)
     sigma, mkProj (Names.Projection.make s false, t')
     (* failwith "todo proj 2" *)
  | Coq_tFix (* of Ast0.term Ast0.mfixpoint * Datatypes.nat *) _ -> todo 7
  | Coq_tCoFix (* of Ast0.term Ast0.mfixpoint * Datatypes.nat *) _ -> todo 8

let rec string_of_term (t : Ast0.term) : string =
  match t with
  | Coq_tRel n -> "Rel " ^ string_of_int (unquote_nat n)
  | Coq_tVar s -> "Var"
  | Coq_tMeta n -> "Meta"
  | Coq_tEvar (n, l) -> "Evar"
  | Coq_tSort Coq_sProp -> "Prop"
  | Coq_tSort Coq_sSet -> "Set"
  | Coq_tSort (Coq_sType _) -> "Type"
  | Coq_tCast (t, k, u) -> "(" ^ string_of_term t ^ ":" ^ string_of_term u ^ ")"
  | Coq_tProd (Coq_nAnon, t, u) -> "Π (" ^ "_" ^ ": " ^ string_of_term t ^ ")." ^ string_of_term u
  | Coq_tProd (Coq_nNamed n, t, u) -> "Π (" ^ string_of_chars n ^ ": " ^ string_of_term t ^ ")." ^ string_of_term u
  | Coq_tLambda (Coq_nAnon, t, u) -> "λ (" ^ "_" ^ ": " ^ string_of_term t ^ ")." ^ string_of_term u
  | Coq_tLambda (Coq_nNamed n, t, u) -> "λ (" ^ string_of_chars n ^ ": " ^ string_of_term t ^ ")." ^ string_of_term u
  | Coq_tLetIn (Coq_nAnon, t, u, v) -> "let " ^ "_" ^ ":= " ^ string_of_term t ^ " : " ^ string_of_term u ^ " in " ^ string_of_term v
  | Coq_tLetIn (Coq_nNamed n, t, u, v) -> "let " ^ string_of_chars n ^ ":= " ^ string_of_term t ^ " : " ^ string_of_term u ^ " in " ^ string_of_term v
  | Coq_tApp (t, l) -> string_of_term t ^ List.fold_left (fun s t -> s ^ "(" ^ string_of_term t ^ ") ") " " l
  | Coq_tConst s -> "Const:" ^ string_of_chars s
  | Coq_tInd (Coq_mkInd (s, _)) -> "Ind:" ^ string_of_chars s
  | Coq_tConstruct (Coq_mkInd (s, _), k) -> "Construct:" ^ string_of_chars s
  | Coq_tCase _ -> "Case"
  | Coq_tProj (((Coq_mkInd (s, _), k), n), t) -> "Proj:" ^ string_of_chars s ^ string_of_int (unquote_nat n) ^ " (" ^ string_of_term t ^ ")"
  | Coq_tFix (* of Ast0.term Ast0.mfixpoint * Datatypes.nat *) _ -> "Fix"
  | Coq_tCoFix (* of Ast0.term Ast0.mfixpoint * Datatypes.nat *) _ -> "Cofix"
