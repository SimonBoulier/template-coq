(*i camlp4deps: "parsing/grammar.cma" i*)
(*i camlp4use: "pa_extend.cmp" i*)

open Ltac_plugin

let contrib_name = "template-coq"
(* open Feedback *)


let toDecl (old: Names.name * ((Constr.constr) option) * Constr.constr) : Context.Rel.Declaration.t =
  let (name,value,typ) = old in 
  match value with
  | Some value -> Context.Rel.Declaration.LocalDef (name,value,typ)
  | None -> Context.Rel.Declaration.LocalAssum (name,typ)

let fromDecl (n: Context.Rel.Declaration.t) :  Names.name * ((Constr.constr) option) * Constr.constr =
  match n with 
  | Context.Rel.Declaration.LocalDef (name,value,typ) -> (name,Some value,typ)
  | Context.Rel.Declaration.LocalAssum (name,typ) -> (name,None,typ)

let cast_prop = ref (false)
let _ = Goptions.declare_bool_option {
  Goptions.optdepr = false;
  Goptions.optname = "Casting of propositions in template-coq";
  Goptions.optkey = ["Template";"Cast";"Propositions"];
  Goptions.optread = (fun () -> !cast_prop);
  Goptions.optwrite = (fun a -> cast_prop:=a);
}

(* whether Set Template Cast Propositions is on, as needed for erasure in Certicoq *)
let is_cast_prop () = !cast_prop                     
                     
let pp_constr fmt x = Pp.pp_with fmt (Printer.pr_constr x)

module TermReify =
struct
  exception NotSupported of Term.constr * string

  module Cmap = Names.KNmap
  module Cset = Names.KNset
  module Mindset = Names.Mindset

  (* flags *)
  let opt_hnf_ctor_types = ref false
  let opt_debug = ref false

  let with_debug f =
    opt_debug := true ;
    try
      let result = f () in
      opt_debug := false ;
      result
    with
      e -> let _ = opt_debug := false in raise e

  let debug (m : unit -> Pp.std_ppcmds) =
    if !opt_debug then
      Feedback.(msg_debug (m ()))
    else
      ()

  let with_hnf_ctor_types f =
    opt_hnf_ctor_types := true ;
    try
      let result = f () in
      opt_hnf_ctor_types := false ;
      result
    with
      e -> let _ = opt_hnf_ctor_types := false in raise e

  open Pp (* this adds the ++ to the current scope *)

  let not_supported evm trm =
    (* Feedback.msg_error (str "Not Supported:" ++ spc () ++ Printer.pr_constr trm) ; *)
    CErrors.user_err (str "Not Supported:" ++ spc () ++ Printer.pr_constr (EConstr.to_constr evm trm))
    (* raise (NotSupported (trm, "no reason")) *)

  let not_supported_verb evm trm rs =
    CErrors.user_err (str "Not Supported raised at " ++ str rs ++ str ":" ++ spc () ++ Printer.pr_constr (EConstr.to_constr evm trm))
    
  let bad_term evm trm =
    raise (NotSupported (EConstr.to_constr evm trm, "bad term"))

  let bad_term_verb evm trm rs =
    raise (NotSupported (EConstr.to_constr evm trm, "bad term because of " ^ rs))

    
  let gen_constant_in_modules locstr dirs s =
    Universes.constr_of_global (Coqlib.gen_reference_in_modules locstr dirs s)

  let resolve_symbol (path : string list) (tm : string) : Globnames.global_reference =
    Coqlib.gen_reference_in_modules contrib_name [path] tm

  (* todo: virer *)
  let is_glob evm t r = Termops.is_global evm r t

  let pkg_bignums = ["Coq";"Numbers";"BinNums"]
  let pkg_datatypes = ["Coq";"Init";"Datatypes"]
  let pkg_reify = ["Template";"Ast"]
  let pkg_string = ["Coq";"Strings";"String"]

  let r_reify = resolve_symbol pkg_reify

  let tString = resolve_symbol pkg_string "String"
  let tEmptyString = resolve_symbol pkg_string "EmptyString"
  let tO = resolve_symbol pkg_datatypes "O"
  let tS = resolve_symbol pkg_datatypes "S"
  let tnat = resolve_symbol pkg_datatypes "nat"
  let ttrue = resolve_symbol pkg_datatypes "true"
  let cSome = resolve_symbol pkg_datatypes "Some"
  let cNone = resolve_symbol pkg_datatypes "None"
  let tfalse = resolve_symbol pkg_datatypes "false"
  let unit_tt = resolve_symbol pkg_datatypes "tt"
  let tAscii = resolve_symbol ["Coq";"Strings";"Ascii"] "Ascii"
  let c_nil = resolve_symbol pkg_datatypes "nil"
  let c_cons = resolve_symbol pkg_datatypes "cons"
  let prod_type = resolve_symbol pkg_datatypes "prod"
  let sum_type = resolve_symbol pkg_datatypes "sum"
  let option_type = resolve_symbol pkg_datatypes "option"
  let bool_type = resolve_symbol pkg_datatypes "bool"
  let cInl = resolve_symbol pkg_datatypes "inl"
  let cInr = resolve_symbol pkg_datatypes "inr"
  let prod a b =
    Term.mkApp (Universes.constr_of_global prod_type, [| a ; b |])   (* todo: fix *)
  let c_pair = resolve_symbol pkg_datatypes "pair"
  let pair a b f s =
    Term.mkApp (Universes.constr_of_global c_pair, [| a ; b ; f ; s |])   (* todo: fix *)

    (* reify the constructors in Template.Ast.v, which are the building blocks of reified terms *)
  let nAnon = r_reify "nAnon"
  let nNamed = r_reify "nNamed"
  let kVmCast = r_reify "VmCast"
  let kNative = r_reify "NativeCast"
  let kCast = r_reify "Cast"
  let kRevertCast = r_reify "RevertCast"
  let sProp = r_reify "sProp"
  let sSet = r_reify "sSet"
  let sType = r_reify "sType"
  let tident = r_reify "ident"
  let tIndTy = r_reify "inductive"
  let tmkInd = r_reify "mkInd"
  let (tTerm,tRel,tVar,tMeta,tEvar,tSort,tCast,tProd,
       tLambda,tLetIn,tApp,tCase,tFix,tConstructor,tConst,tInd,tUnknown, tHole) =
    (r_reify "term", r_reify "tRel", r_reify "tVar", r_reify "tMeta", r_reify "tEvar",
     r_reify "tSort", r_reify "tCast", r_reify "tProd", r_reify "tLambda",
     r_reify "tLetIn", r_reify "tApp", r_reify "tCase", r_reify "tFix",
     r_reify "tConstruct", r_reify "tConst", r_reify "tInd", r_reify "tUnknown", r_reify "tHole")
      
  let (tdef,tmkdef) = (r_reify "def", r_reify "mkdef")
  let (tLocalDef,tLocalAssum,tlocal_entry) = (r_reify "LocalDef", r_reify "LocalAssum", r_reify "local_entry")

  let (cFinite,cCoFinite,cBiFinite) = (r_reify "Finite", r_reify "CoFinite", r_reify "BiFinite")
  let (pConstr,pType,pAxiom,pIn) =
    (r_reify "PConstr", r_reify "PType", r_reify "PAxiom", r_reify "PIn")
  let tinductive_body = r_reify "inductive_body"
  let tmkinductive_body = r_reify "mkinductive_body"

  let tMutual_inductive_entry = r_reify "mutual_inductive_entry"
  let tOne_inductive_entry = r_reify "one_inductive_entry"
  let tBuild_mutual_inductive_entry = r_reify "Build_mutual_inductive_entry"
  let tBuild_one_inductive_entry = r_reify "Build_one_inductive_entry"
  
  let (tmReturn,tmBind,tmQuote,tmQuoteTermRec,tmReduce,tmMkDefinition,tmMkInductive, tmPrint, tmQuoteTerm) =
    (r_reify "tmReturn", r_reify "tmBind", r_reify "tmQuote", r_reify "tmQuoteTermRec", r_reify "tmReduce",
       r_reify "tmMkDefinition", r_reify "tmMkInductive", r_reify "tmPrint", r_reify "tmQuoteTerm")

  let to_positive =
    let xH = Universes.constr_of_global @@ resolve_symbol pkg_bignums "xH" in
    let xO = Universes.constr_of_global @@ resolve_symbol pkg_bignums "xO" in
    let xI = Universes.constr_of_global @@ resolve_symbol pkg_bignums "xI" in
    let rec to_positive n =
      if n = 1 then
	xH
      else
	if n mod 2 = 0 then
	  Term.mkApp (xO, [| to_positive (n / 2) |])
	else
  	  Term.mkApp (xI, [| to_positive (n / 2) |])
    in
    fun n ->
      if n <= 0
      then raise (Invalid_argument ("to_positive: " ^ string_of_int n))
      else to_positive n

  let to_coq_list typ =
    let the_nil = Term.mkApp (Universes.constr_of_global c_nil, [| typ |]) in
    let rec to_list (ls : Term.constr list) : Term.constr =
      match ls with
	[] -> the_nil
      | l :: ls ->
	Term.mkApp (Universes.constr_of_global c_cons, [| typ ; l ; to_list ls |])
    in to_list

  let int_to_nat =
    let cache = Hashtbl.create 10 in
    let rec recurse i =
      try Hashtbl.find cache i
      with
	Not_found ->
	  if i = 0 then
	    let result = Universes.constr_of_global tO in
	    let _ = Hashtbl.add cache i result in
	    result
	  else
	    let result = Term.mkApp (Universes.constr_of_global tS, [| recurse (i - 1) |]) in
	    let _ = Hashtbl.add cache i result in
	    result
    in
    fun i ->
      assert (i >= 0) ;
      recurse i

  let to_coq_bool b = Universes.constr_of_global (if b then ttrue else tfalse)


  let quote_char i =
    Term.mkApp (Universes.constr_of_global tAscii, Array.of_list (List.map (fun m -> to_coq_bool ((i land m) = m))
					 (List.rev [128;64;32;16;8;4;2;1])))

  let chars = Array.init 255 quote_char

  let quote_char c = chars.(int_of_char c)

  let string_hash = Hashtbl.create 420

  let to_string s =
    let len = String.length s in
    let rec go from acc =
      if from < 0 then acc
      else
        let term = Term.mkApp (Universes.constr_of_global tString, [| quote_char (String.get s from) ; acc |]) in
        go (from - 1) term
    in
    go (len - 1) (Universes.constr_of_global tEmptyString)
                      
  let quote_string s =
    try Hashtbl.find string_hash s
    with Not_found ->
      let term = to_string s in
      Hashtbl.add string_hash s term; term

  let quote_ident i =
    let s = Names.string_of_id i in
    quote_string s

  let quote_name n =
    match n with
      Names.Name id -> Term.mkApp (Universes.constr_of_global nNamed, [| quote_ident id |])
    | Names.Anonymous -> Universes.constr_of_global nAnon

  let quote_cast_kind k =
    match k with
      Term.VMcast -> kVmCast
    | Term.DEFAULTcast -> kCast
    | Term.REVERTcast -> kRevertCast
    | Term.NATIVEcast -> kNative

  let quote_universe s =
    match Univ.Universe.level s with
      Some x -> to_string (Univ.Level.to_string x)
    | None -> to_string ""
    (* (\** TODO: This doesn't work yet **\) *)
    (* to_positive 1 *)

  let quote_sort (s : Term.sorts) =
    match s with
    | Term.Prop Term.Null -> Universes.constr_of_global sProp
    | Term.Prop Term.Pos -> Universes.constr_of_global sSet
    | Term.Type u -> Term.mkApp (Universes.constr_of_global sType, [| quote_universe u |])

  let quote_inductive env (t : Names.inductive) =
    let (m,i) = t in
    Term.mkApp (Universes.constr_of_global tmkInd, [| quote_string (Names.string_of_kn (Names.canonical_mind m))
			 ; int_to_nat i |])
               
  let mk_ctor_list =
    let ctor_list =
      let ctor_info_typ = prod (prod (Universes.constr_of_global tident) (Universes.constr_of_global tTerm)) (Universes.constr_of_global tnat) in
      to_coq_list ctor_info_typ
    in
    fun ls ->
    let ctors = List.map (fun (a,b,c) -> pair (prod (Universes.constr_of_global tident) (Universes.constr_of_global tTerm)) (Universes.constr_of_global tnat)
					 (pair (Universes.constr_of_global tident) (Universes.constr_of_global tTerm) a b) c) ls in
      Term.mkApp (Universes.constr_of_global tmkinductive_body, [| ctor_list ctors |])

  let rec pair_with_number st ls =
    match ls with
      [] -> []
    | l :: ls -> (st,l) :: pair_with_number (st + 1) ls

  let hnf_type env ty =
    let rec hnf_type continue ty =
      match Term.kind_of_term ty with
	Term.Prod (n,t,b) -> Term.mkProd (n,t,hnf_type true b)
      | Term.LetIn _
      | Term.Cast _
      | Term.App _ when continue ->
	 hnf_type false (Reduction.whd_all env ty)
      | _ -> ty
    in
    hnf_type true ty

  let push_rel decl (in_prop, env) = (in_prop, Environ.push_rel decl env)
  let push_rel_context ctx (in_prop, env) = (in_prop, Environ.push_rel_context ctx env)

  let castSetProp (sf:Term.sorts) t =
    let sf = Term.family_of_sort sf in
    if sf == Term.InProp 
    then Term.mkApp (Universes.constr_of_global tCast, [| t ; Universes.constr_of_global kCast ; Term.mkApp (Universes.constr_of_global tSort, [| Universes.constr_of_global sProp |]) |])
    else if sf == Term.InSet 
    then Term.mkApp (Universes.constr_of_global tCast, [| t ; Universes.constr_of_global kCast ; Term.mkApp (Universes.constr_of_global tSort, [| Universes.constr_of_global sSet |]) |])
    else t

  let noteTypeAsCast t typ =
    Term.mkApp (Universes.constr_of_global tCast, [| t ; Universes.constr_of_global kCast ; typ |])

  let getSort env (t:Term.constr) =
    Retyping.get_sort_of env Evd.empty (EConstr.of_constr t)

  let getType env (t:Term.constr) : Term.constr =
    EConstr.to_constr Evd.empty (Retyping.get_type_of env Evd.empty (EConstr.of_constr t))

  (* given a term of shape \x1 x2 ..., T, it puts a cast around T if T is a Set or a Prop,
lambdas like this arise in the case-return type in matches, i.e. the part between return and with in
match _  as _ in  _ return __ with *)
  let rec putReturnTypeInfo (env : Environ.env) (t: Term.constr) : Term.constr =
    match Term.kind_of_term t with
    | Term.Lambda (n,t,b) ->
       Term.mkLambda (n,t,putReturnTypeInfo (Environ.push_rel (toDecl (n, None, t)) env) b)
    | _ ->
       let sf =  (getSort env t)  in 
       Term.mkCast (t,Term.DEFAULTcast,Term.mkSort sf)

  let quote_term_remember
      (add_constant : Names.kernel_name -> 'a -> 'a)
      (add_inductive : Names.inductive -> 'a -> 'a) =
    let rec quote_term (acc : 'a) env trm =
      let rec aux acc env trm =
      match Term.kind_of_term trm with
	Term.Rel i -> (Term.mkApp (Universes.constr_of_global tRel, [| int_to_nat (i - 1) |]), acc)
      | Term.Var v -> (Term.mkApp (Universes.constr_of_global tVar, [| quote_ident v |]), acc)
      | Term.Sort s -> (Term.mkApp (Universes.constr_of_global tSort, [| quote_sort s |]), acc)
      | Term.Cast (c,k,t) ->
	let (c',acc) = quote_term acc env c in
	let (t',acc) = quote_term acc env t in
	(Term.mkApp (Universes.constr_of_global tCast, [| c' ; Universes.constr_of_global (quote_cast_kind k) ; t' |]), acc)
      | Term.Prod (n,t,b) ->
	let (t',acc) = quote_term acc env t in
  let sf = getSort (snd env)  t in
  let env = push_rel (toDecl (n, None, t)) env in
  let sfb = getSort (snd env) b in
	let (b',acc) = quote_term acc env b in
	(Term.mkApp (Universes.constr_of_global tProd, [| quote_name n ; castSetProp sf  t' ; castSetProp sfb b' |]), acc)
      | Term.Lambda (n,t,b) ->
	let (t',acc) = quote_term acc env t in
  let sf = getSort (snd env) t  in 
	let (b',acc) = quote_term acc (push_rel (toDecl (n, None, t)) env) b in
       (Term.mkApp (Universes.constr_of_global tLambda, [| quote_name n ; castSetProp sf t' ; b' |]), acc)
      | Term.LetIn (n,e,t,b) ->
	let (e',acc) = quote_term acc env e in
	let (t',acc) = quote_term acc env t in
	let (b',acc) = quote_term acc (push_rel (toDecl (n, Some e, t)) env) b in
	(Term.mkApp (Universes.constr_of_global tLetIn, [| quote_name n ; e'; t' ; b' |]), acc)
      | Term.App (f,xs) ->
	let (f',acc) = quote_term acc env f in
	let (xs',acc) =
	  List.fold_left (fun (xs,acc) x ->
	    let (x,acc) = quote_term acc env x in (x :: xs, acc))
	    ([],acc) (Array.to_list xs) in
	(Term.mkApp (Universes.constr_of_global tApp, [| f' ; to_coq_list (Universes.constr_of_global tTerm) (List.rev xs') |]), acc)
      | Term.Const (c,pu) -> (* FIXME: take universe constraints into account *)
         let kn = Names.Constant.canonical c in
	 (Term.mkApp (Universes.constr_of_global tConst, [| quote_string (Names.string_of_kn kn) |]),
          add_constant kn acc)
      | Term.Construct ((ind,c),pu) ->
         (* FIXME: take universe constraints into account *)
	(Term.mkApp (Universes.constr_of_global tConstructor, [| quote_inductive env ind ; int_to_nat (c - 1) |]), add_inductive ind acc)
      | Term.Ind (i,pu) -> (* FIXME: take universe constraints into account *)
         (Term.mkApp (Universes.constr_of_global tInd, [| quote_inductive env i |]),
          add_inductive i acc)
      | Term.Case (ci,typeInfo,discriminant,e) ->
        let ind = quote_inductive env ci.Term.ci_ind in
        let npar = int_to_nat ci.Term.ci_npar in
        let info = pair (Universes.constr_of_global tIndTy) (Universes.constr_of_global tnat) ind npar in
  let discriminantType = getType (snd env) discriminant in
  let typeInfo = putReturnTypeInfo (snd env) typeInfo in
	let (qtypeInfo,acc) = quote_term acc env typeInfo in
	let (discriminant,acc) = quote_term acc env discriminant in
  let (discriminantType,acc) = (quote_term acc env discriminantType) in
  let discriminant = noteTypeAsCast discriminant discriminantType in 
	let (branches,acc) =
          CArray.fold_left2 (fun (xs,acc) x nargs ->
            let (x,acc) = quote_term acc env x in
            let t = pair (Universes.constr_of_global tnat) (Universes.constr_of_global tTerm) (int_to_nat nargs) x in
              (t :: xs, acc))
          ([],acc) e ci.Term.ci_cstr_nargs in
        let tl = prod (Universes.constr_of_global tnat) (Universes.constr_of_global tTerm) in
        (Term.mkApp (Universes.constr_of_global tCase, [| info ; qtypeInfo ; discriminant ; to_coq_list tl (List.rev branches) |]),
         acc)
      | Term.Fix fp ->
	let (t,n,acc) = quote_fixpoint acc env fp in
	(Term.mkApp (Universes.constr_of_global tFix, [| t ; int_to_nat n |]), acc)
      | _ -> (Term.mkApp (Universes.constr_of_global tUnknown, [| quote_string (Format.asprintf "%a" pp_constr trm) |]), acc)
      in
      let in_prop, env' = env in 
      if is_cast_prop () && not in_prop then
        let ty = Retyping.get_type_of env' Evd.empty (EConstr.of_constr trm) in
        let sf = Retyping.get_sort_family_of env' Evd.empty ty in
        if sf == Term.InProp then
          aux acc (true, env')
              (Term.mkCast (trm, Term.DEFAULTcast,
                            Term.mkCast (EConstr.to_constr Evd.empty ty, Term.DEFAULTcast, Term.mkProp))) 
        else aux acc env trm
      else aux acc env trm
    and quote_fixpoint acc env t =
      let ((a,b),(ns,ts,ds)) = t in
      let rec seq f t =
	if f < t then
	  f :: seq (f + 1) t
	else
	  []
      in
      let ctxt = CArray.map2_i (fun i na t -> (Context.Rel.Declaration.LocalAssum (na, Vars.lift i t))) ns ts in
      let envfix = push_rel_context (Array.to_list ctxt) env in
      let mk_fun (xs,acc) i =
	let n = int_to_nat (Array.get a i) in
	let nm = quote_name (Array.get ns i) in
	let (ty,acc) = quote_term acc env (Array.get ts i) in
	let (ds,acc) = quote_term acc envfix (Array.get ds i) in
	(Term.mkApp (Universes.constr_of_global tmkdef, [| Universes.constr_of_global tTerm ; nm ; ty ; ds ; n |]) :: xs, acc)
      in
      let (defs,acc) = List.fold_left mk_fun ([],acc) (seq 0 (Array.length a)) in
      (to_coq_list (Term.mkApp (Universes.constr_of_global tdef, [| Universes.constr_of_global tTerm |])) (List.rev defs), b, acc)
    and quote_minductive_type (acc : 'a) env (t : Names.mutual_inductive) =
      let mib = Environ.lookup_mind t (snd env) in
      let inst = Univ.UContext.instance mib.Declarations.mind_universes in
      let indtys =
        Array.to_list Declarations.(Array.map (fun oib ->
           let ty = Inductive.type_of_inductive (snd env) ((mib,oib),inst) in
           (Context.Rel.Declaration.LocalAssum (Names.Name oib.mind_typename, ty))) mib.mind_packets)
      in
      let envind = push_rel_context indtys env in
      let (ls,acc) =
	List.fold_left (fun (ls,acc) (n,oib) ->
	  let named_ctors =
	    CList.combine3
	      Declarations.(Array.to_list oib.mind_consnames)
	      Declarations.(Array.to_list oib.mind_user_lc)
	      Declarations.(Array.to_list oib.mind_consnrealargs)
	  in
	  let (reified_ctors,acc) =
	    List.fold_left (fun (ls,acc) (nm,ty,ar) ->
	      debug (fun () -> Pp.(str "XXXX" ++ spc () ++
                            bool !opt_hnf_ctor_types)) ;
	      let ty = if !opt_hnf_ctor_types then hnf_type (snd envind) ty else ty in
	      let (ty,acc) = quote_term acc envind ty in
	      ((quote_ident nm, ty, int_to_nat ar) :: ls, acc))
	      ([],acc) named_ctors
	  in
	  Declarations.((quote_ident oib.mind_typename,
	    mk_ctor_list (List.rev reified_ctors)) :: ls, acc))
	  ([],acc) Declarations.(pair_with_number 0
		      (Array.to_list mib.mind_packets))
      in
      let params = int_to_nat mib.Declarations.mind_nparams in
      (params, to_coq_list (prod (Universes.constr_of_global tident) (Universes.constr_of_global tinductive_body))
	 (List.map (fun (a,b) ->
	   pair (Universes.constr_of_global tident) (Universes.constr_of_global tinductive_body) a b) (List.rev ls)),
       acc)
    in ((fun acc env -> quote_term acc (false, env)),
        (fun acc env -> quote_minductive_type acc (false, env)))

  let quote_term env trm =
    let (fn,_) = quote_term_remember (fun _ () -> ()) (fun _ () -> ()) in
    fst (fn () env trm)

  type defType =
    Ind of Names.inductive
  | Const of Names.kernel_name

  let quote_term_rec env trm =
    let visited_terms = ref Names.KNset.empty in
    let visited_types = ref Mindset.empty in
    let constants = ref [] in
    let add quote_term quote_type trm acc =
      match trm with
      | Ind (mi,idx) ->
	let t = mi in
	if Mindset.mem t !visited_types then ()
	else
	  begin
	    let (params,result,acc) = quote_type acc env mi in
	    let ref_name =
	      quote_string (Names.string_of_kn (Names.canonical_mind mi)) in
	    visited_types := Mindset.add t !visited_types ;
	    constants := Term.mkApp (Universes.constr_of_global pType, [| ref_name; params
					     ; result |]) :: !constants
	  end
      | Const kn ->
	if Names.KNset.mem kn !visited_terms then ()
	else
	  begin
	    visited_terms := Names.KNset.add kn !visited_terms ;
            let c = Names.Constant.make kn kn in
	    let cd = Environ.lookup_constant c env in
	    let do_body body =
	      let (result,acc) =
		quote_term acc (Global.env ()) body
	      in
	      constants := Term.mkApp (Universes.constr_of_global pConstr,
				       [| quote_string (Names.string_of_kn kn)
				       ; result |]) :: !constants
	    in
	    Declarations.(
	      match cd.const_body with
		Undef _ ->
		begin
		  let (ty,acc) =
		    match cd.const_type with
		    | RegularArity ty -> quote_term acc (Global.env ()) ty
		    | TemplateArity _ -> assert false
		  in
		  constants := Term.mkApp (Universes.constr_of_global pAxiom,
					   [| quote_string (Names.string_of_kn kn) ; ty |]) :: !constants
		end
	      | Def cs ->
		do_body (Mod_subst.force_constr cs)
	      | OpaqueDef lc ->
		do_body (Opaqueproof.force_proof (Global.opaque_tables ()) lc))
	  end
    in
    let (quote_rem,quote_typ) =
      let a = ref (fun _ _ _ -> assert false) in
      let b = ref (fun _ _ _ -> assert false) in
      let (x,y) =
	quote_term_remember (fun x () -> add !a !b (Const x) ())
	                    (fun y () -> add !a !b (Ind y) ())
      in
      a := x ;
      b := y ;
      (x,y)
    in
    let (x,acc) = quote_rem () env trm
    in List.fold_left (fun acc x -> Term.mkApp (x, [| acc |]))
                      (Term.mkApp (Universes.constr_of_global pIn, [| x |])) !constants

 let quote_one_ind envA envC (mi:Entries.one_inductive_entry) : Term.constr =
   Entries.(
   let iname = quote_ident mi.mind_entry_typename  in
   let arity = quote_term envA mi.mind_entry_arity in 
   let templatePoly = to_coq_bool mi.mind_entry_template in
   let consnames = to_coq_list (Universes.constr_of_global tident) (List.map quote_ident (mi.mind_entry_consnames)) in
   let cons_types = to_coq_list (Universes.constr_of_global tTerm) (List.map (quote_term envC) (mi.mind_entry_lc)) in
   Term.mkApp (Universes.constr_of_global tBuild_one_inductive_entry, [| iname; arity; templatePoly; consnames; cons_types |]))

let process_local_entry 
  (f: 'a -> Term.constr option (* body *) -> Term.constr (* type *) -> Names.Id.t -> Environ.env -> 'a) 
  ((env,a):(Environ.env*'a)) 
  ((n,le):(Names.Id.t * Entries.local_entry))
  :  (Environ.env * 'a) =
  match le with
  | Entries.LocalAssumEntry t -> (Environ.push_rel (toDecl (Names.Name n,None,t)) env, f a None t n env)
  | Entries.LocalDefEntry b -> 
      let typ = getType env b in
      (Environ.push_rel (toDecl (Names.Name n, Some b, typ)) env, f a (Some b) typ n env)


let quote_mind_params env (params:(Names.Id.t * Entries.local_entry) list)
  :  Environ.env*(Term.constr list)=
  let pair i l = pair (Universes.constr_of_global tident) (Universes.constr_of_global tlocal_entry) i l in 
  let f lr ob t n env =
    match ob with
    | Some b ->  (pair (quote_ident n) (Term.mkApp (Universes.constr_of_global tLocalDef,[|(quote_term env b)|])))::lr
    | None -> 
      let sf = getSort env t  in 
       (pair (quote_ident n) (Term.mkApp (Universes.constr_of_global tLocalAssum,[|castSetProp sf (quote_term env t)|])))::lr in
    let (env, params) = List.fold_left (process_local_entry f) (env,[]) (List.rev params) in (env, List.rev params)
    
let mind_params_as_types ((env,t):Environ.env*Term.constr) (params:(Names.Id.t * Entries.local_entry) list) : 
   Environ.env*Term.constr =
    List.fold_left (process_local_entry (fun tr ob typ n env -> Term.mkProd_or_LetIn (toDecl (Names.Name n,ob,typ)) tr)) (env,t) 
      (List.rev params)

let quote_mind_finiteness (f: Decl_kinds.recursivity_kind) =
  match f with
  | Decl_kinds.Finite -> cFinite
  | Decl_kinds.CoFinite -> cCoFinite
  | Decl_kinds.BiFinite -> cBiFinite
     
let quote_mut_ind  env (mi:Declarations.mutual_inductive_body) : Term.constr =
   let t= Discharge.process_inductive ([],Univ.UContext.empty) (Names.Cmap.empty,Names.Mindmap.empty) mi in
   Entries.(
   let the_prod = Term.mkApp (Universes.constr_of_global prod_type,[|Universes.constr_of_global tident; Universes.constr_of_global tlocal_entry|]) in 
   let mr = Term.mkApp (Universes.constr_of_global cNone, [|Term.mkApp (Universes.constr_of_global option_type, [|Universes.constr_of_global tident|])|])  in
   let mf = quote_mind_finiteness t.mind_entry_finite in 
   let mp = to_coq_list the_prod (snd (quote_mind_params env (t.mind_entry_params))) in
   (* before quoting the types of constructors, we need to enrich the environment with the inductives *)
   let one_arities =
      List.map 
        (fun x -> (x.mind_entry_typename,
           snd (mind_params_as_types (env,x.mind_entry_arity) (t.mind_entry_params)))) 
      t.mind_entry_inds in
  (* env for quoting constructors of inductives. First push inductices, then params *)
   let envC = List.fold_left (fun env p -> Environ.push_rel (toDecl (Names.Name (fst p), None, snd p)) env) env (one_arities) in
   let (envC,_) = List.fold_left (process_local_entry (fun _ _ _ _ _ -> ())) (envC,()) (List.rev (t.mind_entry_params)) in
  (* env for quoting arities of inductives -- just push the params *)
   let (envA,_) = List.fold_left (process_local_entry (fun _ _ _ _ _ -> ())) (env,()) (List.rev (t.mind_entry_params)) in
   let is = to_coq_list (Universes.constr_of_global tOne_inductive_entry) (List.map (quote_one_ind envA envC) (t.mind_entry_inds)) in
   let mpol = tfalse in
   let mpr = Term.mkApp (Universes.constr_of_global cNone, [|Universes.constr_of_global bool_type|]) in
   Term.mkApp (Universes.constr_of_global tBuild_mutual_inductive_entry, [| mr; Universes.constr_of_global mf; mp; is; Universes.constr_of_global mpol; mpr |])
   )

  let split_name s : (Names.DirPath.t * Names.Id.t)=
    let ss = List.rev (Str.split (Str.regexp (Str.quote ".")) s) in
    match ss with
      nm :: rst ->
    	let dp = (Names.make_dirpath (List.map Names.id_of_string rst)) in (dp, Names.Id.of_string nm)
    | [] -> raise (Failure "Empty name cannot be quoted")

  let kn_of_canonical_string s =
    let ss = List.rev (Str.split (Str.regexp (Str.quote ".")) s) in
    match ss with
      nm :: rst ->
	let rec to_mp ls = Names.MPfile (Names.make_dirpath (List.map Names.id_of_string ls)) in
	let mp = to_mp rst in
	Names.make_kn mp Names.empty_dirpath (Names.mk_label nm)
    | _ -> assert false

(*  let quote_decl bypass env evm (name:string) = *)
(*    let opType = Term.mkApp(sum_type, [|tTerm;tMutual_inductive_entry|]) in *)
(*    let mkSome c t = Term.mkApp (cSome, [|opType; Term.mkApp (c, [|tTerm;tMutual_inductive_entry; t|] )|]) in *)
(*    let mkSomeDef = mkSome cInl in *)
(*    let mkSomeInd  = mkSome cInr in *)
(*    let (dp, nm) = split_name name in *)
(* (\*   try *\) *)
(*          Feedback.msg_debug (Pp.str("finding Inductive")); *)
(*    match Nametab.locate (Libnames.make_qualid dp nm) with *)
(*    |Globnames.ConstRef c -> *)
(*       let cd = Environ.lookup_constant c env in *)
(* 	    Declarations.( *)
(* 	      match cd.const_body with *)
(* 		    | Undef _ -> Term.mkApp (cNone, [|opType|]) *)
(* 	      | Def cs -> mkSomeDef (quote_term (Global.env ()) (Mod_subst.force_constr cs)) *)
(* 	      | OpaqueDef cs ->  *)
(*       if bypass  *)
(*       then mkSomeDef (quote_term (Global.env ()) (Opaqueproof.force_proof (Global.opaque_tables ()) cs)) *)
(*       else Term.mkApp (cNone, [|opType|]) *)
(*       ) *)
(*     | Globnames.IndRef ni -> *)
(*         let c = Environ.lookup_mind (fst ni) env in (\* FIX: For efficienctly, we should also export (snd ni)*\) *)
(*          Feedback.msg_debug (Pp.str("found Inductive")); *)
(*         let miq = quote_mut_ind env c in *)
(*         mkSomeInd miq *)
(*     | Globnames.ConstructRef _ -> Term.mkApp (cNone, [|opType|]) (\* FIX: return the enclusing mutual inductive *\) *)
(*     | Globnames.VarRef _ -> (\* what is this *\)Term.mkApp (cNone, [|opType|]) *)
(* (\*    with  *)
(*     Not_found ->  *)
(*           Term.mkApp (cNone, [|opType|])   *\) *)


 (* todo: useless if acc empty *)
  let rec app_full (trm:Term.constr) acc =
    match Term.kind_of_term trm with
      Term.App (f, xs) -> app_full f (Array.to_list xs @ acc)
    | _ -> (trm, acc)

  let rec nat_to_int evm trm =
    let (h,args) = EConstr.decompose_app evm trm in
    if Termops.is_global evm tO h then 0
    else if Termops.is_global evm tS h then
      match args with
      | [ n ] -> 1 + nat_to_int evm n
      | _ -> bad_term_verb evm trm "nat_to_int"
    else
      not_supported_verb evm trm "nat_to_int"

  let from_bool evm trm =
    if Termops.is_global evm ttrue trm then
      true
    else if Termops.is_global evm tfalse trm then
      false
    else not_supported_verb evm trm "from_bool"

  let unquote_char evm trm =
    let (h,args) = EConstr.decompose_app evm trm in
    if Termops.is_global evm tAscii h then
      match args with
      | [ a ; b ; c ; d ; e ; f ; g ; h ] ->
         let bits = List.rev [a;b;c;d;e;f;g;h] in
         let v = List.fold_left (fun a n -> (a lsl 1) lor if from_bool evm n then 1 else 0) 0 bits in
         char_of_int v
      | _ -> bad_term_verb evm trm "unquote_char"
    else
      not_supported_verb evm trm "unquote_char"
(*
let reduce_all env (evm,def) =
  	let (evm2,red) = Tacinterp.interp_redexp env evm (Genredexpr.Cbv Redops.all_flags) in
	  let red = fst (Redexpr.reduction_of_red_expr env red) in
	  red env evm2 def
*)

  (* let reduce_hnf env evm def : Evd.evar_map * EConstr.t = *)
  (*   (evm, Tacred.hnf_constr env evm def) *)

  let reduce_all env (evm, def)  =
     (evm, Redexpr.cbv_vm env evm def)

  let unquote_string evm trm =
    let rec go n trm =
      let (h,args) = EConstr.decompose_app evm trm in
      if is_glob evm h tEmptyString then
        Bytes.create n
      else if is_glob evm h tString then
	match args with
	  c :: s :: _ ->
	    let res = go (n + 1) s in
	    let _ = Bytes.set res n (unquote_char evm c) in
	    res
	| _ -> bad_term_verb evm trm "unquote_string"
      else
	not_supported_verb evm trm "unquote_string"
    in
    Bytes.to_string (go 0 trm)

  let unquote_ident evm trm =
    Names.id_of_string (unquote_string evm trm)

  let unquote_cast_kind evm trm =
    if is_glob evm trm kVmCast then
      Term.VMcast
    else if is_glob evm trm kCast then
      Term.DEFAULTcast
    else if is_glob evm trm kRevertCast then
      Term.REVERTcast
    else if is_glob evm trm kNative then
      Term.VMcast
    else
      bad_term evm trm


  let unquote_name evm trm =
    let (h,args) = EConstr.decompose_app evm trm in
    if is_glob evm h nAnon then
      Names.Anonymous
    else if is_glob evm h nNamed then
      match args with
	n :: _ -> Names.Name (unquote_ident evm n)
      | _ -> raise (Failure "ill-typed, expected name")
    else
      raise (Failure "non-value")

  let unquote_sort evm trm =
    let (h,args) = EConstr.decompose_app evm trm in
    if is_glob evm h sType then
      Term.type1_sort
    else if is_glob evm h sProp then
      Term.prop_sort
    else if is_glob evm h sSet then
      Term.set_sort
    else
      raise (Failure "ill-typed, expected sort")



  let denote_inductive evm trm =
    let (h,args) = EConstr.decompose_app evm trm in
    if is_glob evm h tmkInd then
      match args with
	nm :: num :: _ ->
        let s = (unquote_string evm nm) in
        let (dp, nm) = split_name s in
        (try 
          match Nametab.locate (Libnames.make_qualid dp nm) with
          | Globnames.ConstRef c ->  raise (Failure (String.concat "this not an inductive constant. use tConst instead of tInd : " [s]))
          | Globnames.IndRef i -> (fst i, nat_to_int evm num)
          | Globnames.VarRef _ -> raise (Failure (String.concat "the constant is a variable. use tVar : " [s]))
          | Globnames.ConstructRef _ -> raise (Failure (String.concat "the constant is a consructor. use tConstructor : " [s]))
        with
        Not_found ->   raise (Failure (String.concat "Constant not found : " [s])))
      | _ -> assert false
    else
      raise (Failure "non-constructor")

  let rec from_coq_list evm trm =
    let (h,args) = EConstr.decompose_app evm trm in
    if is_glob evm h c_nil then []
    else if is_glob evm h c_cons then
      match args with
	_ :: x :: xs :: _ -> x :: from_coq_list evm xs
      | _ -> bad_term evm trm
    else
      not_supported_verb evm trm "from_coq_list"




  (* let reduce_all env (evm,def) rd = *)
  (*   let (evm2,red) = Ltac_plugin.Tacinterp.interp_redexp env evm rd in *)
  (*   let red = fst (Redexpr.reduction_of_red_expr env red) in *)
  (*   let Sigma.Sigma (c, evm, _) = red.Reductionops.e_redfun env (Sigma.Unsafe.of_evar_map evm2) def in *)
  (*   Sigma.to_evar_map evm, c *)

  let from_coq_pair evm trm =
    let (h,args) = EConstr.decompose_app evm trm in
    if is_glob evm h c_pair then
      match args with
	_ :: _ :: x :: y :: [] -> (x, y)
      | _ -> bad_term evm trm
    else
      not_supported_verb evm trm "from_coq_pair"

(*
Stm.interp
Vernacentries.interp
Vernacexpr.Check
*)

  (** NOTE: Because the representation is lossy, I should probably
   ** come back through elaboration.
   ** - This would also allow writing terms with holes
   **)
  let rec denote_term env evm (trm : EConstr.t) : Evd.evar_map * EConstr.t=
    debug (fun () -> Pp.(str "denote_term" ++ spc () ++ Printer.pr_econstr_env env evm trm)) ;
    let (h, args) = EConstr.decompose_app evm trm in
    if is_glob evm h tRel then
      match args with
	x :: _ ->
	  (evm, EConstr.mkRel (nat_to_int evm x + 1))
      | _ -> raise (Failure "ill-typed")
    else if is_glob evm h tVar then
      match args with
	x :: _ -> (evm, EConstr.mkVar (unquote_ident evm x))
      | _ -> raise (Failure "ill-typed")
    else if is_glob evm h tSort then
      match args with
	x :: _ -> (evm, EConstr.mkSort (unquote_sort evm x))
      | _ -> raise (Failure "ill-typed")
    else if is_glob evm h tCast then
      match args with
	t :: c :: ty :: _ ->
        let (evm, t') = denote_term env evm t in
        let (evm, ty') = denote_term env evm ty in
	  (evm, EConstr.mkCast (t', unquote_cast_kind evm c, ty'))
      | _ -> raise (Failure "ill-typed")
    else if is_glob evm h tProd then
      match args with
	n :: t :: b :: _ ->
        let (evm, t') = denote_term env evm t in
        let (evm, b') = denote_term env evm b in
	  (evm, EConstr.mkProd (unquote_name evm n, t', b'))
      | _ -> raise (Failure "ill-typed (product)")
    else if is_glob evm h tLambda then
      match args with
	n :: t :: b :: _ ->
        let (evm, t') = denote_term env evm t in
        let (evm, b') = denote_term env evm b in
	  (evm, EConstr.mkLambda (unquote_name evm n, t', b'))
      | _ -> raise (Failure "ill-typed (lambda)")
    else if is_glob evm h tLetIn then
      match args with
	n :: e :: t :: b :: _ ->
        let (evm, e') = denote_term env evm e in
        let (evm, t') = denote_term env evm t in
        let (evm, b') = denote_term env evm b in
      	  (evm, EConstr.mkLetIn (unquote_name evm n, e', t', b'))
      | _ -> raise (Failure "ill-typed (let-in)")
    else if is_glob evm h tApp then
      match args with
	f :: xs :: _ ->
        let (evm, f') = denote_term env evm f in
        let (evm, xs') = List.fold_right (fun x (evm, l) -> let (evm, x') = denote_term env evm x in (evm, x' :: l))
                                         (from_coq_list evm xs) (evm, [])
        in (evm, EConstr.mkApp (f', Array.of_list xs'))
	  (* (evm, EConstr.mkApp (denote_term env evm f, *)
		      (* Array.of_list (List.map (denote_term env evm) (from_coq_list xs)))) *)
      | _ -> raise (Failure "ill-typed (app)")
    else if is_glob evm h tConst then
      match args with
    	s :: [] ->
        let s = (unquote_string evm s) in
        let (dp, nm) = split_name s in
        (try 
          match Nametab.locate (Libnames.make_qualid dp nm) with
          | Globnames.ConstRef c ->  (evm, EConstr.mkConst c)
          | Globnames.IndRef _ -> raise (Failure (String.concat "the constant is an inductive. use tInd : " [s]))
          | Globnames.VarRef _ -> raise (Failure (String.concat "the constant is a variable. use tVar : " [s]))
          | Globnames.ConstructRef _ -> raise (Failure (String.concat "the constant is a consructor. use tConstructor : " [s]))
        with
        Not_found ->   raise (Failure (String.concat "Constant not found : " [s])))

      | _ -> raise (Failure "ill-typed (tConst)")
    else if is_glob evm h tConstructor then
      match args with
	i :: idx :: _ ->
	  let i = denote_inductive evm i in
	  (evm, EConstr.mkConstruct (i, nat_to_int evm idx + 1))
      | _ -> raise (Failure "ill-typed (constructor)")
    else if is_glob evm h tInd then
      match args with
	i :: _ ->
	  let i = denote_inductive evm i in
	  (evm, EConstr.mkInd i)
      | _ -> raise (Failure "ill-typed (inductive)")
    else if is_glob evm h tCase then
      match args with
	info :: ty :: d :: brs :: _ ->
          let i, _ = from_coq_pair evm info in
          let ind = denote_inductive evm i in
          let ci = Inductiveops.make_case_info (Global.env ()) ind Term.RegularStyle in
          let (evm, ty') = denote_term env evm ty in
          let (evm, d') = denote_term env evm d in
          let (evm, brs') = List.fold_right (fun x (evm, l) -> let (evm, x') = denote_term env evm x in (evm, x' :: l))
                                            (List.map (fun y -> snd (from_coq_pair evm y)) (from_coq_list evm brs)) (evm, [])
          in (evm, EConstr.mkCase (ci, ty', d', Array.of_list brs'))
      | _ -> raise (Failure "ill-typed (case)")
    else if is_glob evm h tFix then
      match args with
	    bds :: i :: _ ->
        let unquoteFbd  b : ((Term.constr * Term.constr) * (Term.constr * Term.constr)) =
          let (_,args) = app_full b [] in
          match args with
          | _(*type*)::a::b::c::d::[] -> ((a,b),(c,d))
          |_ -> raise (Failure " (mkdef must take exactly 5 arguments)")
          in
        let lbd = List.map unquoteFbd (from_coq_list evm bds) in
        let (p1,p2) = (List.map fst lbd, List.map snd lbd) in
        let (names,types,bodies,rargs) = (List.map fst p1, List.map snd p1, List.map fst p2, List.map snd p2) in
        let (evm, types') = List.fold_right (fun x (evm, l) -> let (evm, x') = denote_term env evm x in (evm, x' :: l))
                                            types (evm, []) in
        let (evm, bodies') = List.fold_right (fun x (evm, l) -> let (evm, x') = denote_term env evm x in (evm, x' :: l))
                                            bodies (evm, []) in
        let (names,rargs) = (List.map (unquote_name evm) names, List.map (nat_to_int evm) rargs) in
        let la = Array.of_list in
          (evm, EConstr.mkFix ((la rargs,nat_to_int evm i), (la names, la types', la bodies')))
      | _ -> raise (Failure "tFix takes exactly 2 arguments")
    else if is_glob evm h tHole then
      let (evm, (a, _)) = Evarutil.new_type_evar env evm (Evd.UnivFlexible true) in
      Evarutil.new_evar env evm a
    else
      not_supported_verb evm trm "big_case"

(*
  let declare_definition
    (id : Names.Id.t) (loc, boxed_flag, def_obj_kind)
    (binder_list : Constrexpr.local_binder list) red_expr_opt (constr_expr : Constrexpr.constr_expr)
    constr_expr_opt decl_hook =
    Command.do_definition
    id (loc, false, def_obj_kind) None binder_list red_expr_opt constr_expr
    constr_expr_opt decl_hook

  let add_definition name result =
    declare_definition name
	    (Decl_kinds.Global, false, Decl_kinds.Definition)
	    [] None result None (Lemmas.mk_hook (fun _ _ -> ()))
*)




  let unquote_red_add_definition b env evm name def =
	  let (evm,def) = reduce_all env (evm,def) in
  	let trm = if b then snd (denote_term env evm def) else def in
    if b then Feedback.msg_debug ((Printer.pr_constr trm)) else ();
    Declare.declare_definition 
	  ~kind:Decl_kinds.Definition name
	  (trm, (* No new universe constraints can be generated by typing the AST *)
           Univ.ContextSet.empty)
	  
  let denote_local_entry env evm trm =
    let (h,args) = EConstr.decompose_app evm trm in
      match args with
	    x :: [] -> 
      if is_glob evm h tLocalDef then Entries.LocalDefEntry (snd (denote_term env evm x) )
      else (if  is_glob evm h tLocalAssum then Entries.LocalAssumEntry (snd (denote_term env evm x)) else bad_term trm)
      | _ -> bad_term trm

  let denote_mind_entry_finite evm trm =
    let (h,args) = EConstr.decompose_app evm trm in
      match args with
	    [] -> 
      if is_glob evm h cFinite then Decl_kinds.Finite
      else if  is_glob evm h cCoFinite then Decl_kinds.CoFinite
      else if  is_glob evm h cBiFinite then Decl_kinds.BiFinite
      else bad_term trm
      | _ -> bad_term trm

  let unquote_map_option evm f trm =
    let (h,args) = EConstr.decompose_app evm trm in
    if is_glob evm h cSome then 
    match args with
	  _ :: x :: _ -> Some (f x)
      | _ -> bad_term trm
    else if is_glob evm h cNone then 
    match args with
	  _ :: [] -> None
      | _ -> bad_term trm
    else
      not_supported_verb trm "unqote_map_option"


  let declare_inductive (env: Environ.env) (evm: Evd.evar_map) (body: Term.constr) : unit =
  let open Entries in
  let (evm,body) = reduce_all env (evm, body)  (* (Genredexpr.Cbv Redops.all_flags) *) in
  let (_,args) = app_full body [] in (* check that the first component is Build_mut_ind .. *) 
  let one_ind b1 : Entries.one_inductive_entry = 
    let (_,args) = app_full b1 [] in (* check that the first component is Build_one_ind .. *)
    match args with
    | mt::ma::mtemp::mcn::mct::[] ->
       let (evm, ma') = denote_term env evm ma in
       let (evm, mct') = List.fold_right (fun x (evm, l) -> let (evm, x') = denote_term env evm x in (evm, x' :: l))
                                         (from_coq_list mct) (evm, []) in
    {
    mind_entry_typename = unquote_ident mt;
    mind_entry_arity = ma';
    mind_entry_template = from_bool mtemp;
    mind_entry_consnames = List.map unquote_ident (from_coq_list mcn);
    mind_entry_lc = mct'
    } 
    | _ -> raise (Failure "ill-typed one_inductive_entry")
     in 
  let mut_ind mr mf mp mi mpol mpr : Entries.mutual_inductive_entry =
    {
    mind_entry_record = unquote_map_option evm (unquote_map_option evm unquote_ident) mr;
    mind_entry_finite = denote_mind_entry_finite evm mf; (* inductive *)
    mind_entry_params = List.map (fun p -> let (l,r) = (from_coq_pair p) in (unquote_ident l, (denote_local_entry env evm r))) 
      (List.rev (from_coq_list mp));
    mind_entry_inds = List.map one_ind (from_coq_list mi);
    mind_entry_polymorphic = from_bool mpol;
    mind_entry_universes = Univ.UContext.empty;
    mind_entry_private = unquote_map_option evm from_bool mpr (*mpr*)
    } in 
    match args with
    mr::mf::mp::mi::mpol::mpr::[] -> 
      ignore(Command.declare_mutual_inductive_with_eliminations (mut_ind mr mf mp mi mpol mpr) [] [])
    | _ -> raise (Failure "ill-typed mutual_inductive_entry")

  let declare_interpret_inductive (env: Environ.env) (evm: Evd.evar_map) (body: Constrexpr.constr_expr) : unit =
	let (body,_) = Constrintern.interp_constr env evm body in
  declare_inductive env evm body

  let rec run_template_program_rec  ((env,evm,pgm): Environ.env * Evd.evar_map * Term.constr) : Environ.env * Evd.evar_map * Term.constr =
    let pgm = Tacred.hnf_constr env evm pgm in 
    let (coConstr,args) = app_full pgm [] in
    if is_glob evm coConstr tmReturn then
      match args with
      | _::h::[] -> (env,evm,h)
      | _ -> raise (Failure "tmReturn must take 2 arguments. Please file a bug with Template-Coq.")
    else if is_glob evm coConstr tmBind then
      match args with
      | _::_::a::f::[] ->
        let (env, evm, ar) = run_template_program_rec (env,evm,a) in
        run_template_program_rec (env,evm,(EConstr.mkApp (f, Array.of_list [ar])))
      | _ -> raise (Failure "tmBind must take 4 arguments. Please file a bug with Template-Coq.")
    else if is_glob evm coConstr tmMkDefinition then
      match args with
      | b::name::_::body::[] -> 
        let (evm,name) = reduce_all env (evm,name) in
        let (evm,b) = reduce_all env (evm,b) in
        let _ = unquote_red_add_definition (from_bool b) env evm (unquote_ident name) body in (env, evm, unit_tt)
      | _ -> raise (Failure "tmMkDefinition must take 4 arguments. Please file a bug with Template-Coq.")
    else if is_glob evm coConstr tmQuote then
      match args with
      | id::b::[] ->
          let (evm,id) = reduce_all env (evm,id) in
          let (evm,b) = reduce_all env (evm,b) in
          let qt=quote_decl (from_bool b) env evm (unquote_string id) in
          (env, evm, qt)
      | _ -> raise (Failure "tmQuote must take 1 argument. Please file a bug with Template-Coq.")
    else if is_glob evm coConstr tmQuoteTerm then
      match args with
      | _::trm::[] -> let qt = quote_term env trm in (* user should do the reduction (using tmReduce) if they want *)
              (env, evm, qt)
      | _ -> raise (Failure "tmQuoteTerm must take 1 argument. Please file a bug with Template-Coq.")
    else if is_glob evm coConstr tmQuoteTermRec then
      match args with
      | trm::[] -> let qt = quote_term_rec env trm in
              (env, evm, qt)
      | _ -> raise (Failure "tmQuoteTermRec must take 1 argument. Please file a bug with Template-Coq.")
    else if is_glob evm coConstr tmPrint then
      match args with
      | _::trm::[] -> let _ = Feedback.msg_debug ((Printer.pr_constr trm)) in (env, evm, unit_tt)
      | _ -> raise (Failure "tmPrint must take 2 arguments. Please file a bug with Template-Coq.")
    else if is_glob evm coConstr tmReduce then
      match args with
      | _(*reduction strategy*)::_(*type*)::trm::[] -> 
          let (evm,trm) = reduce_all env (evm,trm) in (env, evm, trm)
      | _ -> raise (Failure "tmReduce must take 3 arguments. Please file a bug with Template-Coq.")
    else if is_glob evm coConstr tmMkInductive then
      match args with
      | mind::[] -> let _ = declare_inductive env evm mind in (env, evm, unit_tt)
      | _ -> raise (Failure "tmReduce must take 3 arguments. Please file a bug with Template-Coq.")
    else raise (Failure "Invalid argument or yot yet implemented. The argument must be a TemplateProgram")

  let run_template_program (env: Environ.env) (evm: Evd.evar_map) (body: Constrexpr.constr_expr) : unit =
  	let (body,_) = Constrintern.interp_constr env evm body in
    let _ = run_template_program_rec (env,evm,body) in ()
end

DECLARE PLUGIN "template_plugin"

(** Stolen from CoqPluginUtils **)
(** Calling Ltac **)
let ltac_call tac (args:Tacexpr.glob_tactic_arg list) =
  Tacexpr.TacArg(Loc.tag @@ Tacexpr.TacCall (Loc.tag (Misctypes.ArgArg(Loc.tag @@ Lazy.force tac),args)))

(* let ltac_call tac (args:Tacexpr.glob_tactic_arg list) = *)
(*   Tacexpr.TacArg(Loc.ghost,Tacexpr.TacCall(Loc.ghost, Misctypes.ArgArg(Loc.ghost, Lazy.force tac),args)) *)

(* Calling a locally bound tactic *)
(* let ltac_lcall tac args = *)
(*   Tacexpr.TacArg(Loc.ghost,Tacexpr.TacCall(Loc.ghost, Misctypes.ArgVar(Loc.ghost, Names.id_of_string tac),args)) *)
let ltac_lcall tac args =
  Tacexpr.TacArg(Loc.tag @@ Tacexpr.TacCall (Loc.tag (Misctypes.ArgVar(Loc.tag @@ Names.Id.of_string tac),args)))

(* let ltac_letin (x, e1) e2 = *)
(*   Tacexpr.TacLetIn(false,[(Loc.ghost,Names.id_of_string x),e1],e2) *)

open Names
open Tacexpr
open Tacinterp
open Misctypes

   
let ltac_apply (f : Value.t) (args: Tacinterp.Value.t list) =
  let fold arg (i, vars, lfun) =
    let id = Id.of_string ("x" ^ string_of_int i) in
    let x = Reference (ArgVar (Loc.tag id)) in
    (succ i, x :: vars, Id.Map.add id arg lfun)
  in
  let (_, args, lfun) = List.fold_right fold args (0, [], Id.Map.empty) in
  let lfun = Id.Map.add (Id.of_string "F") f lfun in
  let ist = { (Tacinterp.default_ist ()) with Tacinterp.lfun = lfun; } in
  Tacinterp.eval_tactic_ist ist (ltac_lcall "F" args)

(* let ltac_apply (f:Tacexpr.glob_tactic_expr) (args:Tacexpr.glob_tactic_arg list) = *)
(*   Tacinterp.eval_tactic *)
(*     (ltac_letin ("F", Tacexpr.Tacexp f) (ltac_lcall "F" args)) *)

let to_ltac_val c = Tacinterp.Value.of_constr c

let to_ltac_val c = Tacinterp.Value.of_constr c
(** From Containers **)
let declare_definition
    (id : Names.Id.t) (loc, boxed_flag, def_obj_kind)
    (binder_list) red_expr_opt constr_expr
    constr_expr_opt decl_hook =
  Command.do_definition
  id (loc, false, def_obj_kind) None binder_list red_expr_opt constr_expr
  constr_expr_opt decl_hook

let check_inside_section () =
  if Lib.sections_are_opened () then
    (** In trunk this seems to be moved to Errors **)
    (* For Coq 8.7: CErrors.user_err ~hdr:"Quote" (Pp.str "You can not quote within a section.") *)
    CErrors.errorlabstrm "Quote" (Pp.str "You can not quote within a section.")
  else ()

open Stdarg
open Tacarg
open Proofview.Notations
open Pp

TACTIC EXTEND get_goal
    | [ "quote_term" constr(c) tactic(tac) ] ->
      [ (** quote the given term, pass the result to t **)
  Proofview.Goal.nf_enter begin fun gl ->
          let env = Proofview.Goal.env gl in
	  let c = TermReify.quote_term env (EConstr.to_constr (Proofview.Goal.sigma gl) c) in
	  ltac_apply tac (List.map to_ltac_val [EConstr.of_constr c])
  end ]
(*
    | [ "quote_goal" ] ->
      [ (** get the representation of the goal **)
	fun gl -> assert false ]
    | [ "get_inductive" constr(i) ] ->
      [ fun gl -> assert false ]
*)
END;;


VERNAC COMMAND EXTEND Make_vernac CLASSIFIED AS SIDEFF
    | [ "Quote" "Definition" ident(name) ":=" constr(def) ] ->
      [ check_inside_section () ;
	let (evm,env) = Lemmas.get_current_context () in
	let def = Constrintern.interp_constr env evm def in
	let trm = TermReify.quote_term env (fst def) in
	ignore(Declare.declare_definition ~kind:Decl_kinds.Definition name
                                          (trm, Univ.ContextSet.empty)) ]
END;;

VERNAC COMMAND EXTEND Make_vernac_reduce CLASSIFIED AS SIDEFF
    | [ "Quote" "Definition" ident(name) ":=" "Eval" red_expr(rd) "in" constr(def) ] ->
      [ check_inside_section () ;
	let (evm,env) = Lemmas.get_current_context () in
	let def, uctx = Constrintern.interp_constr env evm def in
        let evm = Evd.from_ctx uctx in
	let (evm2,def) = TermReify.reduce_all env (evm, def) in
	let trm = TermReify.quote_term env (def) in (* TODO: Check that this is evm2 *)
	ignore(Declare.declare_definition ~kind:Decl_kinds.Definition
                                          name (trm, Univ.ContextSet.empty)) ]
END;;

VERNAC COMMAND EXTEND Make_recursive CLASSIFIED AS SIDEFF
    | [ "Quote" "Recursively" "Definition" ident(name) ":=" constr(def) ] ->
      [ check_inside_section () ;
	let (evm,env) = Lemmas.get_current_context () in
	let def = Constrintern.interp_constr env evm def in
	let trm = TermReify.quote_term_rec env (fst def) in
	ignore(Declare.declare_definition 
	  ~kind:Decl_kinds.Definition name
	  (trm, (* No new universe constraints can be generated by typing the AST *)
           Univ.ContextSet.empty)) ]
END;;

TACTIC EXTEND denote_term
    | [ "denote_term" constr(c) tactic(tac) ] ->
       [ Proofview.Goal.nf_enter begin fun gl ->
             let env = Proofview.Goal.env gl in
             let evmr = ref (Proofview.Goal.sigma gl) in
             Typing.e_check env evmr c (EConstr.of_constr TermReify.tTerm);
	     let (evm, trm) = TermReify.denote_term env !evmr c in
             let trm = EConstr.of_constr trm in
             (* let (evm, _) = Typing.type_of env evm trm in *)
             (* let evmr = ref evm in *)
             (* let trm = Typing.e_solve_evars env evmr trm in *)
	     ltac_apply tac [to_ltac_val trm]
             (* let (evm, c) = TermReify.denote_term env evm (EConstr.to_constr (Proofview.Goal.sigma gl) c) in *)
             (* let c' = Constrextern.extern_constr true env evm c in *)
             (* let c = Constrintern.interp_constr env evm c' in *)
	     (* ltac_apply tac (List.map to_ltac_val [EConstr.of_constr (fst c)]) *)
         end ]
END;;

VERNAC COMMAND EXTEND Unquote_vernac CLASSIFIED AS SIDEFF
    | [ "Make" "Definition" ident(name) ":=" constr(def) ] ->
      [ check_inside_section () ;
        let env = Global.env () in
	let (def', ctx) = Constrintern.interp_constr env (Evd.from_env env) def in
        let evmr = ref (Evd.from_ctx ctx) in
        Typing.e_check env evmr (EConstr.of_constr def') (EConstr.of_constr TermReify.tTerm);
	let (evm, trm) = TermReify.denote_term env !evmr def' in
        let trm = EConstr.of_constr trm in
        let (evm, _) = Typing.type_of env evm trm in
        let evmr = ref evm in
        let trm = Typing.e_solve_evars env evmr trm in
        ignore (Declare.declare_definition name (EConstr.to_constr !evmr trm, Evd.universe_context_set evm))
	(* let (evm,env) = Lemmas.get_current_context () in *)
	(* let (def', ctx) = Constrintern.interp_constr env evm def in *)
	(* let (evm, trm) = TermReify.denote_term env (Evd.from_ctx ctx) def' in *)
	(* let result = Constrextern.extern_constr true env evm trm in *)
	(* declare_definition name *)
	(*   (Decl_kinds.Global, false, Decl_kinds.Definition) *)
	(*   [] None result None (Lemmas.mk_hook (fun _ _ -> ())) *)
      ]
END;;

VERNAC COMMAND EXTEND Unquote_inductive CLASSIFIED AS SIDEFF
    | [ "Make" "Inductive" constr(def) ] ->
      [ check_inside_section () ;
	let (evm,env) = Lemmas.get_current_context () in
  TermReify.declare_interpret_inductive env evm def ]
END;;

VERNAC COMMAND EXTEND Run_program CLASSIFIED AS SIDEFF
    | [ "Run" "TemplateProgram" constr(def) ] ->
      [ check_inside_section () ;
	let (evm,env) = Lemmas.get_current_context () in
  TermReify.run_template_program env evm def ]
END;;

VERNAC COMMAND EXTEND Make_tests CLASSIFIED AS QUERY
(*
    | [ "Make" "Definitions" tactic(t) ] ->
      [ (** [t] returns a [list (string * term)] **)
	assert false ]
*)
    | [ "Test" "Quote" constr(c) ] ->
      [ check_inside_section () ;

	let (evm,env) = Lemmas.get_current_context () in
	let c = Constrintern.interp_constr env evm c in
	let result = TermReify.quote_term env (fst c) in
(* DEBUGGING
	let back = TermReify.denote_term env evm result in
	Format.eprintf "%a\n" pp_constr result ;
	Format.eprintf "%a\n" pp_constr back ;
	assert (is_glob evm c back) ;
*)
        Feedback.msg_notice (Printer.pr_constr result) ;
	() ]
END;;
