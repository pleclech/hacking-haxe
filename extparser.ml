open Ast

exception Display of expr

let use_extended_syntax = ref false

type token_stream = (token*pos) Stream.t

let warning : (string -> pos -> unit) ref = ref (fun _ _ -> assert false)

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
let toplevel_expr_ref:(token_stream -> expr) ref = ref (fun _ -> assert false)
let display_ref:(expr -> expr) ref = ref (fun _ -> assert false)

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
}

let ext_current_flag = ref 0
let empty_ext_state() = {es_exprs=Queue.create(); es_for_ctx=[]; es_cfs=Queue.create(); es_cc=[]; es_flags=[]; }

let ext_states = ref []

let ext_state = ref (empty_ext_state())

let ext_init_code = ref (Queue.create())

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

let inside_cc_flag = 1

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

let insert_expr ?(with_semi=true) (es:expr list) =
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
	| [(Kwd KConst, p); (Kwd In, _)] | [(Kwd Val, p); (Kwd In, _)]  ->
		None
	| [(Kwd KConst, p); (Kwd _, _)] | [(Kwd KConst, p); (Const(Ident _), _)]
	| [(Kwd Val, p); (Kwd _, _)] | [(Kwd Val, p); (Const(Ident _), _)] ->
		Some p
	| _ ->
	 	None

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

let parse_cc_opt_access = parser
	| [< '(Kwd Private, _) >] -> [APrivate]
	| [< '(Kwd Public, _) >] -> [APublic]
	| [< >] -> [APublic]

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


let mk_cc_fun ?(is_inlined=false) fun_name cc p1 p2 =
	let mk_arg = function
		| {cca_arg=(_, _, (n, b, ot, oe)); _} -> (n,b,ot,oe,[])
	in
	let init = List.rev (Queue.fold (fun a e -> e::a) [] cc.cc_code) in
	let args = List.map mk_arg cc.cc_args in
	let al = if is_inlined then AInline::cc.cc_al else cc.cc_al in
	mk_cff_fun fun_name cc.cc_meta al cc.cc_constraints args (EBlock init) p1 p2

let mk_cc_f p cc =
	let mk_arg = function
		| {cca_arg=(_, _, (n, b, ot, oe)); _} -> (n,b,ot,oe,[])
	in
	let init = List.rev (Queue.fold (fun a e -> e::a) [] cc.cc_code) in
	let args = List.map mk_arg cc.cc_args in
	{
		f_params = cc.cc_constraints;
		f_args = args;
		f_type = None;
		f_expr = Some (EBlock init, p);
	}


let update_cfs class_name occ fl p1 p2 = match occ with
	| Some cc ->
		if not (List.exists (fun cf -> match cf with {cff_name="new"; cff_kind=FFun _; _} -> true | _ -> false) fl) then begin
			(mk_cc_fun "new" cc p1 p2)::fl
		end else
			fl
	| _ -> fl

let  parse_opt_class_body p1 name =
	if (!use_extended_syntax) then parser
		| [< '(Semicolon,p) >] -> pending_cfs [], p
		| [< '(BrOpen,_); fl, p2 = (!parse_class_fields_ref) false p1 >] ->
				(*let allow_init cf = cf.cff_meta <- ((Meta.Custom "allow_init"),[],null_pos) :: cf.cff_meta in
				List.iter (fun c -> match c with | {cff_kind=FVar _; } as cf -> allow_init cf | {cff_kind=FProp _; } as cf -> allow_init cf | _ -> ()) fl;*)
			fl, p2
	else parser
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
					if s.s_redeclared_cnt==0 then
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
			if no_local && s.s_redeclared_cnt==0 then
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

let parse_class_constructor class_name cp s =
	let cc =
		if !use_extended_syntax then begin
			match s with parser
			| [< meta=(!parse_meta_ref); acl=parse_cc_opt_access; s >] ->
				if meta=[]&&acl=[] then None
				else match s with parser
					| [< '(POpen,o1); s >] ->
						let ss = empty_ext_symbol() in
						ext_init_code := Queue.create();
						ext_symbols := ss;
						(match s with parser
						| [< arl=psep Comma parse_cc_param; '(PClose,o2) >] ->
							Some {cc_meta=meta; cc_al=acl; cc_args=arl; cc_symbols=ss; cc_code=(!ext_init_code); cc_constraints=cp; })
					| [< >] -> None
			| [< >] -> None
		end else None
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
			match with_cc_do (mk_cc_f (pos e)) with
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