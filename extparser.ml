open Ast

exception Display of expr

let use_extended_syntax = ref false

type token_stream = (token*pos) Stream.t

let warning : (string -> pos -> unit) ref = ref (fun _ _ -> assert false)

let serror() = raise (Stream.Error "") 

let replace input output =
    Str.global_replace (Str.regexp_string input) output

let rec psep sep f = parser
	| [< v = f; s >] ->
		let rec loop = parser
			| [< '(sep2,_) when sep2 = sep; v = f; l = loop >] -> v :: l
			| [< >] -> []
		in
		v :: loop s
	| [< >] -> []

let parse_meta_ref:(?is_const:bool -> token_stream -> metadata) ref = ref (fun ?is_const _ -> assert false)
let dollar_ident_ref:(token_stream -> string*pos) ref = ref (fun _ -> assert false)
let parse_type_opt_ref:(token_stream ->complex_type option) ref = ref (fun _ -> assert false)
let parse_fun_param_value_ref:(token_stream -> expr option) ref = ref (fun _ -> assert false)
let parse_class_fields_ref:(bool -> pos -> token_stream -> class_field list*pos) ref = ref ( fun _ _ _ -> assert false)
let make_binop_ref:(binop -> expr -> expr -> expr)  ref = ref (fun _ _ _ -> assert false)
let parse_call_params_ref:(expr -> token_stream -> expr list) ref = ref (fun _ _ -> assert false)
let expr_ref:(token_stream -> expr) ref = ref (fun _ -> assert false)
let secure_expr_ref:(token_stream -> expr) ref = ref (fun _ -> assert false)
let expr_next_ref:(expr -> token_stream -> expr) ref = ref (fun _ _ -> assert false)
let toplevel_expr_ref:(token_stream -> expr) ref = ref (fun _ -> assert false)
let display_ref:(expr -> expr) ref = ref (fun _ -> assert false)
let parse_string_ref:(Common.context -> string -> pos -> bool -> string list * (type_def * pos) list) ref = ref (fun _ _ _ _ -> assert false)
let type_module_with_decls_ref:(Typecore.typer -> Type.path -> string -> type_decl list -> pos -> Type.module_def) ref = ref (fun _ _ _ _ _ -> assert false)
let load_instance_ref:(Typecore.typer -> type_path -> pos -> bool -> Type.t) ref = ref (fun _ _ _ _ -> assert false)
let add_dependency_ref:(Type.module_def -> Type.module_def -> unit) ref = ref (fun _ _ -> assert false)
let parse_var_decl_head_ref:(token_stream -> string * complex_type option * metadata) ref = ref (fun _ -> assert false)
let parse_var_assignment_ref:(token_stream -> expr option) ref = ref (fun _ -> assert false)
let parse_fun_param_ref:(token_stream -> string * bool * complex_type option * expr option * metadata) ref = ref (fun _ -> assert false)

let mk_efield e n p = EField (e, n), p
let mk_eblock b p = EBlock b, p
let mk_eident n p = (EConst(Ident n), p)
let mk_estring n p = (EConst(String n), p)
let mk_eint i p = (EConst(Int (string_of_int i)), p)
let mk_mconst p = (Meta.Const, [], p)
let mk_ecall fn fa pfn = ECall (mk_eident fn pfn, fa), pfn
let mk_eassign e1 e2 = (!make_binop_ref) OpAssign e1 e2
let mk_ethis_assign fn pfn =
	let e_this = mk_eident "this" pfn in
	let e_this = (EField (e_this, fn) , pfn) in
	mk_eassign e_this (mk_eident fn pfn)
let mk_emergeblock blk p =
	EMeta((Meta.MergeBlock, [], p), (EBlock blk, p)), p

type 'a stream_state_t = {
	mutable ss_q: 'a Queue.t; (* priority queue *)
	mutable ss_q_cnt:int; (* peek count *)
	mutable ss_is:'a Stream.t; (* input token stream *)
	mutable ss_is_cnt:int; (* peek count *)
	mutable ss_os:'a Stream.t; (* output stream : mixed of queue and stream *)
	mutable ss_os_cnt:int; (* output stream discarded count *)
	mutable ss_itq_cnt:int; (* number of priority token in the queue *)
	mutable ss_itp_cnt:int; (* number of priority token in the peek buffer *)
}

let ss:(token*pos) stream_state_t option ref = ref None

let dump_token ?(pfx="") ?(sfx="") ls =
	let rp = ref null_pos in
	let s = String.concat " " (List.map (fun (t, p) -> rp:=p; s_token t) ls) in
	!warning (pfx^s^sfx) !rp

let insert_token (ts:(token*pos) list) =
	match !ss with
	| None -> ()
	| Some ss ->
		let rec scopy i s q =
			if i > 0 then begin
				Queue.push (Stream.next s) q;
				scopy (i-1) s q
			end
		in
		let qcopy i q1 q2 =
			if i > 0 && q1!=q2 then
				let rec loop i =
					if i > 0 then begin
						Queue.push (Queue.pop q1) q2;
						loop (i-1)
					end
				in loop i
		in
		let consumed =  (Stream.count ss.ss_os - ss.ss_os_cnt) in
		let pb_cnt =
			let i = ss.ss_itp_cnt - consumed in
			ss.ss_itp_cnt <- if i <= 0 then 0 else i;
			let t = ss.ss_is_cnt + ss.ss_q_cnt - consumed in
			if t <= 0 then 0 else t
		in
		let q1 = ss.ss_q in
		let itp_cnt = ss.ss_itp_cnt in
		let itq_cnt = ss.ss_itq_cnt in
		(*let s = Printf.sprintf "pbc:%d cfc:%d kqc:%d sc:%d oc:%d itq:%d itp:%d" pb_cnt itp_cnt itq_cnt (Stream.count ss.ss_os) ss.ss_os_cnt ss.ss_itq_cnt ss.ss_itp_cnt
		in !warning s null_pos;*)
		let q2 = if (Queue.length q1)<>itq_cnt then Queue.create() else q1 in
		scopy itp_cnt ss.ss_os q2;
		ss.ss_itq_cnt <- ss.ss_itq_cnt + itp_cnt;
		qcopy itq_cnt q1 q2;
		List.iter (fun t -> Queue.push t q2) ts;
		ss.ss_itq_cnt <- ss.ss_itq_cnt + (List.length ts);
		scopy (pb_cnt-itp_cnt) ss.ss_os q2;
		if q1!=q2 then begin
			qcopy (Queue.length q1) q1 q2;
			ss.ss_q <- q2;
		end;
		ss.ss_q_cnt <- 0;
		ss.ss_is_cnt <- 0;
		ss.ss_itp_cnt <- 0;
		(*dump_token ~pfx:("after queue("^(string_of_int ss.ss_itq_cnt)^") ") (List.rev (Queue.fold (fun t a -> a::t) [] ss.ss_q));*)
		ss.ss_os_cnt <- Stream.count ss.ss_os

type class_constructor_arg_t = {
	cca_arg:access list * pos * (string * bool * complex_type option * expr option);
	cca_meta:metadata;
	mutable cca_is_local:bool;
	cca_is_mutable:bool;
}

type symbol_t = {
	s_name:string;
	s_cca:class_constructor_arg_t;
	mutable s_redeclared_cnt:int;
}

type symbols_t = {
	mutable ss_can_access_local:bool;
	mutable ss_depth:int;
	mutable ss_redeclared_names:string list list;
	ss_table:(string , symbol_t) Hashtbl.t
}

type class_constructor_t = {
	cc_al:access list;
	cc_meta:metadata;
	cc_args:class_constructor_arg_t list;
	cc_symbols:symbols_t;
	cc_code:expr Queue.t;
	cc_constraints:type_param list;
}

type ext_state_t = {
	mutable es_exprs:expr Queue.t;
	mutable es_for_ctx:expr option list;
	mutable es_cfs:class_field Queue.t;
	mutable es_cc:class_constructor_t option list;
	mutable es_flags:int list;
	mutable es_uid:int;
	mutable es_ofs:class_field list;
	mutable es_cd:string * pos;
	mutable es_pkg:string list;
}

let ext_current_flag = ref 0
let empty_ext_state() = {es_exprs=Queue.create(); es_for_ctx=[]; es_cfs=Queue.create(); es_cc=[]; es_flags=[]; es_uid=0; es_ofs=[]; es_cd="",null_pos; es_pkg=[]}

let ext_states = ref []

let ext_state = ref (empty_ext_state())

let ext_init_code = ref (Queue.create())

let new_uid() =
	let id = (!ext_state).es_uid + 1 in
	(!ext_state).es_uid <- id;
	id

let fresh_name pfx = pfx^(string_of_int (new_uid()))

let is_flag_set f fs = (fs land f) <> 0
let set_flag f fs = fs lor f
let clear_flag f fs = (fs land (lnot f))
let push_flag f =
		(!ext_state).es_flags <- (!ext_current_flag)::(!ext_state).es_flags;
		ext_current_flag := f
let pop_flag() = match (!ext_state).es_flags with
	| x :: xs ->
		(!ext_state).es_flags <- xs;
		ext_current_flag := x
	| _ -> ext_current_flag := 0

let set_and_push_flag f = push_flag (set_flag f !ext_current_flag)
let clear_and_push_flag f = push_flag (clear_flag f !ext_current_flag)
let is_current_flag_set f = is_flag_set f !ext_current_flag
let set_current_flag f = ext_current_flag := (set_flag f !ext_current_flag)
let clear_current_flag f = ext_current_flag := (clear_flag f !ext_current_flag)

let inside_cc_flag = 1
let pop_expr_flag = 2
let obj_decl_flag = 4
let disallow_sl_flag = 8

let empty_ext_symbol() = {ss_can_access_local=true; ss_depth=0; ss_table=Hashtbl.create 0; ss_redeclared_names=[[]]; }
let default_ext_symbol = empty_ext_symbol()
let ext_symbols = ref (default_ext_symbol)

let save_ext_state() =
	ext_states := !ext_state :: !ext_states;
	ext_state := empty_ext_state();
	ext_current_flag := 0

let restore_ext_state() =
	match !ext_states with
	| x :: xs ->
		ext_states := xs;
		ext_state := x;
		let f =
			match x.es_flags with
			| i::is -> i
			| _ -> 0
		in ext_current_flag := f
	| _ -> ()

let update_symbols_from_cc occ =
	ext_symbols := match occ with
		| None -> default_ext_symbol
		| Some cc -> cc.cc_symbols

let add_symbol s cca = Hashtbl.add (!ext_symbols.ss_table) s {s_name=s; s_redeclared_cnt=0; s_cca=cca; }
let remove_symbol s = Hashtbl.remove (!ext_symbols.ss_table) s

let push_cc occ =
		(!ext_state).es_cc <- occ::(!ext_state).es_cc;
		match occ with
		| None ->
			ext_symbols := default_ext_symbol;
			set_and_push_flag 0
		| Some cc ->
			ext_symbols := cc.cc_symbols;
			set_and_push_flag inside_cc_flag

let pop_cc() = (match (!ext_state).es_cc with
	| x::xs -> 
		(!ext_state).es_cc <- xs;
		update_symbols_from_cc x
	| _ ->
		update_symbols_from_cc None);
	pop_flag()

let insert_exprs ?(with_semi=true) (es:expr list) =
		let q = (!ext_state).es_exprs in
		let insert e = 
			Queue.push e q;
			if with_semi then insert_token [Semicolon, pos e]
		in
		List.iter insert es

let is_expr_available() = not (Queue.is_empty (!ext_state).es_exprs)
let pop_expr() = Queue.pop (!ext_state).es_exprs

let insert_cf (cf:class_field) = Queue.push cf (!ext_state).es_cfs
let is_cf_available() = not (Queue.is_empty (!ext_state).es_cfs)
let pop_cf() = Queue.pop (!ext_state).es_cfs
let pending_cfs acc =
	let q = (!ext_state).es_cfs in
	let rec loop acc =
		if Queue.is_empty q then List.rev acc
		else loop ((Queue.pop q)::acc)
	in loop acc


let token_stream stream =
	let tq = Queue.create() in
	let st = {ss_q=tq; ss_q_cnt=0; ss_is=stream; ss_is_cnt=0; ss_os=stream; ss_os_cnt=0; ss_itq_cnt=0; ss_itp_cnt=0; } in
	let next ss i =
		let t =
			if Queue.is_empty ss.ss_q then begin
				ss.ss_is_cnt <- ss.ss_is_cnt + 1;
				Stream.next ss.ss_is
			end else begin
				ss.ss_q_cnt <- ss.ss_q_cnt + 1;
				ss.ss_is_cnt <- 0;
				if ss.ss_itq_cnt > 0 then begin
					ss.ss_itq_cnt <- ss.ss_itq_cnt - 1;
					ss.ss_itp_cnt <- ss.ss_itp_cnt + 1;
				end;
				Queue.pop ss.ss_q
			end
		in
		Some t
	in
	let s = Stream.from (next st) in
	st.ss_os <- s;
	ss := Some st;
	s

let add_const_init al e =
	let al = List.filter (fun (_,_,_,_,m) -> Meta.has Meta.Const m) al in
	match al with
	| [] -> e
	| _ ->
		let p = pos e in
		let al = List.map (fun (n,_,_,_,_) -> mk_efield (mk_eident n p) "__to_const__" p) al in
		match e with
		| EBlock b, pb -> mk_eblock (al@b) pb
		| _ -> mk_eblock (al@[e]) p

let const_pos s = match Stream.npeek 2 s with
	| [Kwd KConst, p; t] | [Kwd Val, p; t] ->
		(match fst t with
		| Kwd In -> None
		| POpen | Const(Ident _) | Kwd _ -> Some p
		| _ -> None)
	| _ -> None

let reserved_kwd_allowed = parser
	| [< '(Kwd Val,p) >] -> "val", p
	| [< '(Kwd KConst,p) >] -> "const", p
	| [< '(Kwd Def,p) >] -> "def", p

let add_parsed_const ?(junk=true) meta s =
	let sp = const_pos s in
	match  sp with
	| Some p ->
		if junk then Stream.junk s;
		(mk_mconst p)::meta, sp
	| None -> meta, sp

let mk_type pack name params sub =
	{
		tpackage = List.rev pack;
		tname = name;
		tparams = params;
		tsub = sub;
	}

let mk_type_inf pack =
	mk_type pack "Dynamic" ([TPType(CTPath {tpackage=[];tname="_";tparams=[];tsub=None;})]) None


let to_pseudo_private cn fl =
	let tfr_field cf =
		if Meta.has Meta.Private cf.cff_meta then begin
			let ac = APrivate::(List.filter(fun c -> (c<>APrivate)&&(c<>APublic)) cf.cff_access) in
			cf.cff_access <- ac;
			cf.cff_meta <- (Meta.Native, [mk_estring ("_"^(String.lowercase cn)^"_"^cf.cff_name) cf.cff_pos], cf.cff_pos)::cf.cff_meta;
		end
	in List.iter tfr_field fl

let push_for_ctx (a:expr option) = (!ext_state).es_for_ctx <- a ::  (!ext_state).es_for_ctx
let pop_for_ctx() = match (!ext_state).es_for_ctx with
	| [] -> ()
	| x::xs -> (!ext_state).es_for_ctx <- xs
let peek_for_ctx() = match (!ext_state).es_for_ctx with
	| [] -> None
	| x::xs -> x

let ext_expr hx s =
	if is_expr_available() then
		pop_expr()
	else
		hx s

let rec parse_cc_opt_access ?(allow_inline=true) ?(allow_access=true) s = match s with parser
	| [< '(Kwd Private, _) when allow_access; s>] -> APrivate::(parse_cc_opt_access ~allow_access:false ~allow_inline:allow_inline s)
	| [< '(Kwd Public, _) when allow_access; s>] -> APublic::(parse_cc_opt_access ~allow_access:false ~allow_inline:allow_inline s)
	| [< '(Kwd Inline, _) when allow_inline; s >] -> AInline::(parse_cc_opt_access  ~allow_access:allow_access ~allow_inline:false s)
	| [< >] -> if allow_access then [APublic] else []

let parse_cc_param_opt_access = parser
	| [< '(Kwd Private, _) >] -> [APrivate]
	| [< '(Kwd Public, _) >] -> [APublic]
	| [< >] -> [APublic]

let parse_cc_param_opt_modifier = parser
	| [< '(Kwd Var, _) >] -> false, true
	| [< '(Kwd KConst, _) >] -> false, false
	| [< '(Kwd Val, _) >] -> false, false
	| [< >] -> true, false

let mk_cff_fun fun_name meta ac cp args body p1 p2 =
	let f =
	{
		f_params = cp;
		f_args = args;
		f_type = None;
		f_expr = Some(body, p2);
	} 
	in
	{
		cff_name = fun_name;
		cff_doc = None;
		cff_meta = meta;
		cff_access = ac;
		cff_pos = punion p1 p2;
		cff_kind = FFun f;
	}


let mk_cc_fun ?(is_inlined=false) ?(ignore_cp=false) fun_name cc p1 p2 =
	let mk_arg = function
		| {cca_arg=(_, _, (n, b, ot, oe)); _} -> (n,b,ot,oe,[])
	in
	let init = List.rev (Queue.fold (fun a e -> e::a) [] cc.cc_code) in
	let args = List.map mk_arg cc.cc_args in
	let al = if is_inlined then AInline::cc.cc_al else cc.cc_al in
	let cp = if ignore_cp then [] else cc.cc_constraints in
	mk_cff_fun fun_name cc.cc_meta al cp args (EBlock init) p1 p2

let mk_cc_f ?(ignore_cp=false) p cc =
	let mk_arg = function
		| {cca_arg=(_, _, (n, b, ot, oe)); _} -> (n,b,ot,oe,[])
	in
	let init = List.rev (Queue.fold (fun a e -> e::a) [] cc.cc_code) in
	let args = List.map mk_arg cc.cc_args in
	let cp = if ignore_cp then [] else cc.cc_constraints in
	{
		f_params = cp;
		f_args = args;
		f_type = None;
		f_expr = Some (EBlock init, p);
	}


let update_cfs class_name occ fl p1 p2 = match occ with
	| Some cc ->
		if not (List.exists (fun cf -> match cf with {cff_name="new"; cff_kind=FFun _; _} -> true | _ -> false) fl) then begin
			(mk_cc_fun ~ignore_cp:true "new" cc p1 p2)::fl
		end else
			fl
	| _ -> fl

let add_object_def es n p =
	let enew = ENew ({tparams=[];tsub=None;tname=n;tpackage=[]}, []), null_pos in
	let cf =
		{
			cff_name = n;
			cff_meta = [];
			cff_access = [APublic; AStatic];
			cff_doc = None;
			cff_kind = FVar (None, Some enew);
			cff_pos = null_pos;
		}
	in
	es.es_ofs <- cf::es.es_ofs

let add_classdecl n p =
	let es = !ext_state in
	es.es_cd <- n,p;
	if is_current_flag_set obj_decl_flag then ignore(add_object_def es n p)
	else ()

let object_name = "HxObjects"

let get_filename n =
	match List.rev (ExtString.String.nsplit n ".") with
	| _::n::ns ->
		let n = replace "\\" "/" n in
		(match List.rev (ExtString.String.nsplit n "/") with
		| x::xs -> x
		| _ -> n)
	| _ -> ""

let  parse_opt_class_body p1 name s =
	add_classdecl name p1;
	if (!use_extended_syntax) then match s with parser
		| [< '(Semicolon,p) >] -> pending_cfs [], p
		| [< '(BrOpen,_); fl, p2 = (!parse_class_fields_ref) false p1 >] ->
				(*let allow_init cf = cf.cff_meta <- ((Meta.Custom "allow_init"),[],null_pos) :: cf.cff_meta in
				List.iter (fun c -> match c with | {cff_kind=FVar _; } as cf -> allow_init cf | {cff_kind=FProp _; } as cf -> allow_init cf | _ -> ()) fl;*)
			fl, p2
	else match s with parser
		| [< '(BrOpen,_); fl, p2 = (!parse_class_fields_ref) false p1 >] -> fl, p2

let type_or_infer ot = if ot=None then Some(CTPath (mk_type_inf [])) else ot

let add_cc_arg_to_cf cca =
	if cca.cca_is_local then begin
		cca.cca_is_local <- false;
		let al, p, (name, opt, ot, oe) = cca.cca_arg in
		remove_symbol name;
		let t = type_or_infer ot in
		let k = 
			if cca.cca_is_mutable then FVar(t, None)
			else FProp("default", "never", t, None)
		in
		let cf = {cff_name = name; cff_doc = None; cff_meta = (Meta.AllowWrite , [mk_eident "new" p], p)::(Meta.AllowInitInCC, [], p)::cca.cca_meta; cff_access = al; cff_pos = p; cff_kind = k;} in
		Queue.push (mk_ethis_assign name p) !ext_init_code;
		insert_cf cf
	end;
	cca

let declared_symbols ns =
	if is_current_flag_set inside_cc_flag then
		let ss = !ext_symbols in
		let ht = ss.ss_table in
		let rec loop ns =
			match ns with
			| n::ns ->
				begin try
					let s = Hashtbl.find ht n in
					if s.s_redeclared_cnt=0 then
						let _,p,_ = s.s_cca.cca_arg in
						!warning ("Shadowing constructor parameter " ^ n) p;
						s.s_redeclared_cnt <- s.s_redeclared_cnt + 1;
						(match ss.ss_redeclared_names with
						| x::xs -> ss.ss_redeclared_names <- (n::x)::xs
						| [] -> ss.ss_redeclared_names <- [[n]])
				with Not_found -> ()
				end;
				loop ns
			| _ -> ()
		in loop ns
	else ()

let undeclared_symbol pop_scope o_can_access_local =
	if is_current_flag_set inside_cc_flag then
		let ss = !ext_symbols in
		if pop_scope then ss.ss_depth <- ss.ss_depth - 1;
		(match o_can_access_local with
		| Some b -> ss.ss_can_access_local <- b
		| _ -> ());
		let ht = ss.ss_table in
		let ns = (match ss.ss_redeclared_names with
			| x::xs ->
				if pop_scope then ss.ss_redeclared_names <- xs;
				x
			| [] as a -> a)
		in
		let loop ls =
			match ls with
			| x::xs ->
				(try
					let s = Hashtbl.find ht x in
					s.s_redeclared_cnt <- s.s_redeclared_cnt - 1
				with Not_found -> ())
			| _ -> ()
		in loop ns
	else ()

let enter_new_scope o_can_access_local =
	if is_current_flag_set inside_cc_flag then
		let ss = !ext_symbols in
		ss.ss_depth <- ss.ss_depth + 1;
		(match o_can_access_local with
		| Some b -> ss.ss_can_access_local <- b
		| _ -> ());
		ss.ss_redeclared_names <- ([])::ss.ss_redeclared_names

let leave_scope o_can_access_local =
	undeclared_symbol true o_can_access_local

let use_symbol n =
	if is_current_flag_set inside_cc_flag then
		try
			let ss = !ext_symbols in
			let no_local = not ss.ss_can_access_local in
			let s = Hashtbl.find ss.ss_table n in
			if no_local && s.s_redeclared_cnt=0 then
				let _ = add_cc_arg_to_cf s.s_cca in ()
		with Not_found -> ()
	else ()

let use_expr e =
	if is_current_flag_set inside_cc_flag then
		match e with
		| EConst(Ident n), _ ->
			use_symbol n;
			e
		| EField ((EConst (Ident "this"), _), n), _ ->
			use_symbol n;
			e
		| _ -> e
	else e

let declared_in_expr e =
	if is_current_flag_set inside_cc_flag then
		match e with
		| EVars vs , _ ->
			declared_symbols (List.map (fun (n,_,_,_) -> n) vs);
			e
		| _ -> e
	else e


let parse_cc_param_with_ac meta ac (il, im) s =
	let is_opt = match s with parser
		| [< '(Question,_) >] -> true
		| [< >] -> false
	in
	match s with parser
	| [< name, pn=(!dollar_ident_ref); t=(!parse_type_opt_ref); c=(!parse_fun_param_value_ref) >] ->
		let meta = if il then (Meta.Private, [], pn)::meta else meta in
		let arg = {cca_arg=(ac, pn, (name, is_opt, t, c)); cca_meta=meta; cca_is_local=true; cca_is_mutable=im; } in
		if il then begin
			add_symbol name arg;
			arg
		end
		else add_cc_arg_to_cf arg

let parse_cc_param = parser
	| [< meta=(!parse_meta_ref); ac=parse_cc_param_opt_access; m=parse_cc_param_opt_modifier; s >] -> parse_cc_param_with_ac meta ac m s

let parse_class_constructor class_name cp p custom_error s =
	let mk_data() =
		let ss = empty_ext_symbol() in
		let ic = Queue.create() in
		ext_symbols := ss;
		ext_init_code := ic;
		ss, ic
	in
	let mk_cc meta acl arl cp (ss, ic) =
		Some {cc_meta=meta; cc_al=acl; cc_args=arl; cc_symbols=ss; cc_code=(!ext_init_code); cc_constraints=cp; }
	in
	let cc =
		if !use_extended_syntax then
			match s with parser
			| [< meta=(!parse_meta_ref); acl=parse_cc_opt_access; s >] ->
				(*if meta=[]&&acl=[] then None
				else *)
					(match s with parser
					| [< '(POpen,o1); s >] ->
						let data = mk_data() in
						(match s with parser
						|[< arl=psep Comma parse_cc_param; '(PClose,o2) >] -> mk_cc meta acl arl cp data)
					| [< >] -> None)
			| [< >] -> None
		else None
	in
	let cc =
		if is_current_flag_set obj_decl_flag then
			let aname = object_name::(!ext_state).es_pkg in
			let aname = String.concat "." (List.rev aname) in
			match cc with
			| Some c ->
				if cp<>[] then custom_error "No constraint parameter allowed in object declaration" p;
				if c.cc_args<>[] then custom_error "No parameters allowed in object constructor" p;
				let acl = APrivate::AInline::(List.filter(fun a -> a<>APublic) c.cc_al) in
				let meta = (Meta.Allow,[mk_eident aname p],p)::c.cc_meta in
				Some {c with cc_meta=meta; cc_al=acl; }
			| _ ->
				mk_cc [(Meta.Allow,[mk_eident aname p],p)] [APrivate; AInline] [] [] (mk_data())
		else cc
	in
	push_cc cc;
	cc

let insert_cc_expr cc e = Queue.push e cc.cc_code

let with_cc_do f =
	match (!ext_state).es_cc with
	| (Some cc)::xs -> Some (f cc)
	| _ -> None

let insert_exprs_in_cc el =
	let f cc =
		let q = cc.cc_code in
		List.iter (fun e -> Queue.push e q) el
	in with_cc_do f

let mk_init_field n e p =
	if !use_extended_syntax then
		let e = mk_eassign (mk_eident n p) e in 
		let _ = insert_exprs_in_cc [e] in ()

let mk_delayed_init is_cc name e t p =
	if is_cc then begin
		(match e with
		| Some e -> mk_init_field name e p
		| _ -> ());
		None, type_or_infer t, p
	end else e, t, p

let dummy_cf = "",null_pos, FVar (None, None),[],None

let parse_cc_code failed semicolon s =
	if !use_extended_syntax then
		try
			match s with parser
			| [< e = (!expr_ref); s >] ->
				semicolon s;
				let _ = insert_exprs_in_cc [e] in
				dummy_cf
			| [< '(Semicolon,p) >] -> dummy_cf
			| [< >] -> failed()
		with Display e ->
			let _ = insert_exprs_in_cc [e] in
			match with_cc_do (mk_cc_f ~ignore_cp:true (pos e)) with
			| None -> dummy_cf
			| Some f -> "new", pos e, FFun f, [], None
	else
		failed()

let parse_cc_extends occ s =
	if !use_extended_syntax then begin
		match occ with
		| Some cc ->
			(match s with parser
			| [< '(POpen, p1); s >] ->
				let super = (mk_eident "super" p1) in
				let _ = match s with parser
					| [< params = (!parse_call_params_ref) super; '(PClose,p2) >] ->
						let super_call = ECall (super, params), punion p1 p2 in
						(*cc.cc_super = Some (ECall (super, params), punion p1 p2)*)
						insert_cc_expr cc super_call
				in ()
			| [< >] -> ())
		| _ -> ()
	end;
	()

let filter_class_fields fl =
	List.filter (fun cf -> match cf with {cff_name=""; _} -> false | _ -> true) fl

let get_typename name sub params =
	if !use_extended_syntax then
		let ln = (List.length params) in
		match name, sub with
		| "Tuple", None when ln > 0 ->
			name^(string_of_int ln)
		| _ -> name
	else name

let re_tuple = Str.regexp "^Tuple\\([0-9]+\\)$"

let mk_tuple_name i = "Tuple"^(string_of_int i)

let get_tuple_arity s =
	try
		ignore(Str.search_forward re_tuple s 0);
		int_of_string (Str.matched_group 1 s)
	with Not_found -> 0

let create_tuple ctx arity =
	let cn = mk_tuple_name arity in
	let mk_args ?(sfx="") n l =
		let mk_arg i =
			let s_i = string_of_int i in
			let s = n ^ s_i in
			if sfx="" then s else s^sfx^s_i
		in
		let rec loop i acc =
			if i<=0 then acc
			else loop (i-1) ((mk_arg i) ::acc)
		in loop l []
	in
	let s_args ?(sfx="") ?(sep=",") n = String.concat sep (mk_args ~sfx:sfx n arity) in
	let params = s_args "T" in
	let args = s_args ~sfx:":T" "val _" in
	let s = Printf.sprintf "interface I%s<%s> extends Tuple {%s;}\n" cn params (s_args ~sfx:":T" ~sep:";" "val _") in
	let s = s^(Printf.sprintf "@:generic @:final class %s<%s> inline (%s) implements I%s<%s> {\n" cn params args cn params) in
	let body = ref [] in
	body := (Printf.sprintf "public val arity=%d;" arity)::!body;
	body := (Printf.sprintf "inline public def toString()='(%s)';" (s_args "$_"))::!body;
	body := (Printf.sprintf "inline public def toArray():Array<Dynamic>=[%s];" (s_args "_"))::!body;
	let s = s^(String.concat "\n" !body)^"\n}" in
	let f = Printf.sprintf "%s.ehx" cn in
	let p = { pfile=f; pmin=0; pmax=String.length s; } in
	let ues = ctx.Common.use_extended_syntax in
	ctx.Common.use_extended_syntax <- true;
	try
		let ret = (!parse_string_ref) ctx s p true, cn, p in
		ctx.Common.use_extended_syntax <- ues;
		ret
	with e ->
		ctx.Common.use_extended_syntax <- ues;
		raise e

let create_type_on_fly ctx tname error =
	let i = get_tuple_arity tname in
	if i <= 0 then error()
	else
		let (pack, decls), cn, p = create_tuple ctx.Typecore.com i in
		(!type_module_with_decls_ref) ctx ([], cn) p.pfile decls p

let par_cnt = ref 0
let par_cnt_stack = ref []
let save_par_cnt() =
	par_cnt_stack := !par_cnt::!par_cnt_stack;
	par_cnt := 0
let restore_par_cnt() = match !par_cnt_stack with
	| x::xs ->
		par_cnt_stack := xs;
		par_cnt := x
	| [] -> par_cnt := 0
let open_par s = incr par_cnt
let close_par s = decr par_cnt
let sl_is_allowed() = (not (is_current_flag_set disallow_sl_flag)) || (!par_cnt >= 1)

let make_short_lambda_expr pl al st p s =
	let make e =
			let pe = pos e in
			let e = add_const_init al e in
			let e = EBlock [e], pe in
			let e = EReturn (Some e), pe in
			let f = {
				f_params = pl;
				f_type = st;
				f_args = al;
				f_expr = Some e;
			} in
			EFunction (None, f), punion p pe
	in
	try
		(!expr_next_ref) (make ((!secure_expr_ref) s)) s
	with
		Display e -> raise (Display (make e))

let parse_short_lambda_body pl al p = parser
	| [< st = !parse_type_opt_ref; '(Binop OpArrow, _); s >] -> make_short_lambda_expr pl al st p s

let parse_short_lambda_args pl args p1 s =
	match s with parser
	| [< '(Comma, _); s >] ->
		let rec loop acc = match s with parser
		| [< arg=(!parse_fun_param_ref); s >] ->
			(match s with parser
			| [< '(PClose, _); _=close_par; s >] ->
				let args = List.rev (arg::acc) in
				parse_short_lambda_body pl args p1 s
			| [< '(Comma, _) >] -> loop (arg::acc))
		| [< >] -> serror()
		in loop args

let checktype_or_short_lambda_args e t p1 = parser
	| [< '(PClose, p2); _=close_par; s >] ->
		let hx() = (!expr_next_ref) (EParenthesis (ECheckType(e, t),punion p1 p2), punion p1 p2) s in
		if !use_extended_syntax && sl_is_allowed() then
			match Stream.peek s with
			| Some (Binop OpArrow, _) | Some (DblDot, _) ->
				(match e with
				| EConst (Ident n), _ ->
					let args = [n, false, Some t, None, []] in
					parse_short_lambda_body [] args p1 s
				| _ -> hx())
			| _ -> hx()
		else hx()
	| [< s >] ->
		if !use_extended_syntax then
			match e with
			| EConst(Ident n), _ when sl_is_allowed() -> parse_short_lambda_args [] [(n, false, Some t, None, [])] p1 s 
			| _ -> serror()
		else
			serror()

let maybe_short_lambda e p s = match e with
	| EParenthesis (EConst(Ident n), _), _ when sl_is_allowed() -> make_short_lambda_expr [] [(n, false, None, None, [])] None p s
	| _ -> serror()


let rec expr_to_fun_arg meta acc = function
	| EConst (Ident n), _ -> (n, false, None, None, meta)::acc
	| EVars [n, ot, oe, m], _ -> (n, false, ot, oe, (List.rev_append m meta))::acc
	| EParenthesis e, _ -> expr_to_fun_arg meta acc e
	| EMeta((name, params, pm), e), _ -> expr_to_fun_arg ((name, params, pm)::meta) acc e
	| _ -> []

let binop_or_short_lambda op e1 e2 =
	let mk_binop() = (!make_binop_ref) op e1 e2 in
	let mk_fun pl al st =
			let pe = pos e2 in
			let e = add_const_init al e2 in
			let e = EBlock [e], pe in
			let e = EReturn (Some e), pe in
			let f = {
				f_params = pl;
				f_type = st;
				f_args = al;
				f_expr = Some e;
			} in
			EFunction (None, f), punion (pos e1) pe
	in
	match  op with
	| OpArrow when !use_extended_syntax && sl_is_allowed() ->
		let args = expr_to_fun_arg [] [] e1 in
		if args=[] then mk_binop()
		else mk_fun [] args None
	| _ -> mk_binop()

let empty_var = ("", None, None, [])

let rec expr_to_var meta ot = function
	| EConst (Ident n), _ -> n, ot, None, meta
	| EMeta ((n, pms, p), e), _ -> expr_to_var ((n, pms, p)::meta) ot e
	| _ -> empty_var

let parenthesis_or_type e p s =
	let expr() = (!expr_next_ref) (EParenthesis e, p) s in
	if !use_extended_syntax && sl_is_allowed() then
		match Stream.peek s with
		| Some (DblDot, _) ->
			begin match (!parse_type_opt_ref) s with
					| Some t -> (!expr_next_ref) (ECheckType (e, t), p) s
					| _ -> expr()
			end
		| _ -> expr()
	else expr()

let type_or_nothing e s =
	if !use_extended_syntax && sl_is_allowed() then
		match Stream.peek s with
		| Some (DblDot, _) ->
			let (vn, vot, voe, vm) =expr_to_var [] None e in
			if vn="" then e
			else
				begin match (!parse_type_opt_ref) s with
					| (Some t) as ot -> EVars [vn, ot, None, vm], pos e
					| _ -> e
				end
		| _ -> e
	else e

let rec parse_tuple_expr acc s =
	let mk_block lst =
		let lst = List.rev lst in
		EBlock lst, pos (List.hd lst)
	in
	match s with parser
	| [< e = (!expr_ref); s >] ->
		begin match s with parser
			| [< '(Comma, _); l = parse_tuple_expr (e::acc) >] -> l
			| [< >] ->
				begin match Stream.peek s with
					| Some (DblDot, _) ->
						begin match e with
							| EConst(Ident n), _ ->
								let st = (!parse_type_opt_ref) s in
								begin match st with
									 | Some t ->
									 	let acc = List.map (fun e -> match e with
										 	| EConst(Ident n), _ -> (n, false, None, None, [])
										 	| _ -> serror()) acc
									 	in
									 	let acc = (n, false, st, None, [])::acc in
									 	(match Stream.peek s with
									 	| Some (PClose, _) ->
									 		Stream.junk s;
									 		let args = List.rev acc in
											parse_short_lambda_body [] args (pos e) s
										| _ -> parse_short_lambda_args [] acc (pos e) s)
									 | _ -> mk_block (e::acc)
								end
							| _ -> mk_block (e::acc)
						end
					| _ -> mk_block (e::acc)
				end
		end
	| [< >] -> mk_block acc

let tuple_or_enew t al p custom_error s =
	let next() = (!expr_next_ref) (ENew (t,al), p) s in
	if !use_extended_syntax then begin
		match Stream.peek s with
		| Some (Binop OpAssign, _) when (get_tuple_arity t.tname)>0&& t.tparams=[] && t.tsub=None ->
			(match (!parse_var_assignment_ref) s with
			| Some(ae) as sae ->
				let blk = ref [] in
				let ae = match ae with
					| EConst (Ident _), p -> ae
					| _, p ->
						let vn = fresh_name "__td" in
						blk := (EVars [vn, None, sae, [Meta.Const,[],p]], p)::!blk;
						mk_eident vn p
				in
				let pae = pos ae in
				let index = ref 0 in
				List.iter (fun e ->
					incr index;
					match e with
					| EConst (Ident "_"), _ -> ()
					| _ ->
						let ef = EField (ae, ("_" ^ (string_of_int !index))), pae in
						blk := (mk_eassign e ef)::!blk
				) al;
				let bpe = punion p pae in
				EMeta((Meta.MergeBlock, [], bpe), (EBlock (List.rev (!blk)), bpe)), bpe
			| _ ->
				let _ = custom_error "Assignment required for tuple extractor" p in
				EVars [], null_pos
			)
		| _ -> next()
	end else next()

let parse_tuple p1 e error custom_error s =
	if !use_extended_syntax then match s with parser
		| [< '(Comma, _); es=parse_tuple_expr [e]; s >] -> 
			(match es with
			| EBlock es, _ ->
				(match s with parser
				| [<' (PClose,p2); _=close_par; s>] ->
					begin match Stream.peek s with
						| Some (Binop OpArrow, _) | Some (DblDot, _) when sl_is_allowed() ->
							let args = List.map (fun e -> match e with
								| EConst(Ident n), _ -> (n, false, None, None, [])
								| _ -> serror()) es
							in
							parse_short_lambda_body [] args p1 s
						| _ ->
							let cnt = List.length es in
							let t = mk_type [] (mk_tuple_name cnt) [] None in
							tuple_or_enew t (List.rev es) (punion p1 p2) custom_error s
					end
				| [< >] -> error())
			| _ -> es)
		| [< >] -> error()
	else error()

let parse_tuple_head ?(is_const=false) index s =
	let name, t, meta = (!parse_var_decl_head_ref) s in
	let meta = if is_const then (Meta.Const,[],null_pos)::meta else meta in
	name, t, index, meta

let rec parse_tuple_assigment_next ?(is_const=false) vl index = parser
	| [< '(Comma,p1); s; >] ->
		(match Stream.peek s with
		| Some(t, _)  when t=PClose -> vl
		| _ -> 
			(match s with parser 
			| [< name,t, i, meta = parse_tuple_head ~is_const:is_const index; s >] ->
				begin try
					let vl = if name="_" then vl else (name, t, i, meta)::vl in
					parse_tuple_assigment_next vl (i+1) s
				with Display e ->
					let v = name,t,None, meta in
					let vl = List.map (fun (n,t,i,m) -> n,t,None,m) vl in
					let e = (EVars(List.rev (v :: vl)),punion p1 (pos e)) in
					raise (Display e)
				end
			| [< >] -> vl))
	| [< >] -> vl

let parse_tuple_assignment ?(is_const=false) index = parser
	| [< name, t, i, meta = parse_tuple_head ~is_const:is_const index; s >] ->
		let acc = if name="_" then [] else [name, t, i, meta] in
		parse_tuple_assigment_next ~is_const:is_const acc (i+1) s

let parse_tuple_deconstruct ?(is_const=false) custom_error = parser
	| [< '(POpen, p1) when !use_extended_syntax; l=parse_tuple_assignment ~is_const:is_const 1; '(PClose, p2); s >] ->
		(match (!parse_var_assignment_ref) s with
		| Some(ae) as sae ->
			let pae = pos ae in
			let ae = match ae with
				| EConst (Ident _), p -> ae
				| _, p ->
					let vn = fresh_name "__td" in
					insert_exprs ~with_semi:false [(EVars [vn, None, sae, [Meta.Const, [], pae] ], p)];
					set_and_push_flag pop_expr_flag;
					mk_eident vn p
			in
			List.map (fun (n,t,i,m) ->
				let ef = EField (ae, ("_" ^ (string_of_int i))) in
				let e = Some (ef, pae) in
				n,t,e,m
			) l
		| _ -> custom_error "Assignment required for tuple extractor" p1)

let tuple_or_ecall e params p custom_error s =
	let pe = pos e in
	let next() = (!expr_next_ref) (ECall (e,params) , punion pe p) s in
	if !use_extended_syntax then
		let l = List.length params in
		match e with
		| EConst(Ident n), _ when l>0 && (n="val" || n="const") ->
			let m = [Meta.Const, [], pos e] in
			(match Stream.peek s with
			| Some (Binop OpAssign, _) ->
				let empty = "", None, 0, [] in
				let index = ref 0 in
				let rec from_expr meta = function
					| EConst(Ident n), _ ->
						incr index;
						if n="_" then empty else n, None, !index, meta
					| EMeta((name, params, pm), e), _ -> from_expr ((name, params, pm)::meta) e
					| e -> custom_error "Invalid parameter for tuple extractor" (pos e)
				in
				let fl = List.map (from_expr m) params in
				let fl = List.filter(fun (n,_,_,_) -> n<>"") fl in
				(match (!parse_var_assignment_ref) s with
				| Some(ae) as sae ->
					let blk = ref [] in
					let ae = match ae with
						| EConst (Ident _), p -> ae
						| _, p ->
							let vn = fresh_name "__td" in
							blk := (EVars [vn, None, sae, m], p)::!blk;
							mk_eident vn p
					in
					let pae = pos ae in
					let vl = List.map (fun (n,t,i,m) ->
						let ef = EField (ae, ("_" ^ (string_of_int i))) in
						let ae = Some (ef, pae) in
						n,t,ae,m
					) fl
					in
					let bpe = punion pe pae in
					let evars = (EVars vl, bpe) in
					(match !blk with
					| [] -> evars
					| blk -> mk_emergeblock (List.rev (evars::blk)) bpe)
				| _ ->
					let _ = custom_error "Assignment required for tuple extractor" pe in
					EVars [], null_pos
				)
			| _ -> next())
		| _ -> next()
	else next()

let merge_or_expr e =
	if is_current_flag_set pop_expr_flag then
		let e2 = pop_expr() in
		let e = mk_emergeblock [e2; e] (punion (pos e2) (pos e)) in
		pop_flag();
		e
	else e

let is_static_allowed() = not (is_current_flag_set obj_decl_flag)

let is_function_allowed name p1 custom_error s =
	if is_current_flag_set obj_decl_flag then
		match name with
		| "new" ->
			custom_error ("No constructor allowed in object declaration") p1;
			false
		| _ -> true
	else true

let is_extend_allowed p1 custom_error s = true
	(*if is_current_flag_set obj_decl_flag then begin
		custom_error ("You can't extend an object declaration") p1;
		false
	end else true*)

let augment_decls pack decls =
	let es = !ext_state in
	if (List.length es.es_ofs) > 0 then
		let p = (snd es.es_cd) in
		let pname = pack@[(get_filename p.pfile);object_name] in
		let pname = List.map(fun n -> n,null_pos) pname in
		let decls = (EImport (pname,IAll), null_pos)::decls in
		let ho = EClass {
			d_name = object_name;
			d_doc = None;
			d_meta = [Meta.Final,[],null_pos];
			d_params = [];
			d_flags = [];
			d_data = es.es_ofs;
		}, p
		in
		pack, decls@[ho]
	else
		pack, decls

let set_package pack s =
	(!ext_state).es_pkg = pack

let disallow_sl_without_parenthesis s =
	save_par_cnt();
	set_and_push_flag disallow_sl_flag
let allow_sl_without_parenthesis s =
	restore_par_cnt();
	pop_flag()
