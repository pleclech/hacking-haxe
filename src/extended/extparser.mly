open Ast
open Globals
open Refs

exception Display of expr

let mk_efield e n p = EField (e, n), p
let mk_eblock b p = EBlock b, p
let mk_eident n p = (EConst(Ident n), p)
let mk_estring n p = (EConst(String n), p)
let mk_eint i p = (EConst(Int (string_of_int i)), p)
let mk_metaval p = (Meta.Val, [], p)
let mk_ecall fn fa pfn = ECall (mk_eident fn pfn, fa), pfn
let mk_eassign e1 e2 = (!make_binop_ref) OpAssign e1 e2
let mk_ethis_assign fn pfn =
	let e_this = mk_eident "this" pfn in
	let e_this = (EField (e_this, fn) , pfn) in
	mk_eassign e_this (mk_eident fn pfn)
let mk_emergeblock blk p =
	EMeta((Meta.MergeBlock, [], p), (EBlock blk, p)), p
let mk_enull p = (EConst (Ident "null"),p)

let str_replace input output =
    Str.global_replace (Str.regexp_string input) output

let rec psep sep f = parser
	| [< v = f; s >] ->
		let rec loop = parser
			| [< '(sep2,_) when sep2 = sep; v = f; l = loop >] -> v :: l
			| [< >] -> []
		in
		v :: loop s
	| [< >] -> []

let has_meta m ml = List.exists (fun (m2,_,_) -> m = m2) ml

let mk_type pack name params sub =
	{
		tpackage = List.rev pack;
		tname = name;
		tparams = params;
		tsub = sub;
	}

let mk_type_inf ?(p=null_pos) pack =
	mk_type pack "Dynamic" ([TPType(CTPath {tpackage=[];tname="?";tparams=[];tsub=None;}, p)]) None

let type_or_infer ?(p=null_pos) ot = if ot=None then Some((CTPath (mk_type_inf ~p:p []), p)) else ot

let get_filename n =
	match List.rev (ExtString.String.nsplit n ".") with
	| _::n::ns ->
		let n = str_replace "\\" "/" n in
		(match List.rev (ExtString.String.nsplit n "/") with
		| x::xs -> x
		| _ -> n)
	| _ -> ""

type class_constructor_arg_t = {
	cca_arg:access list * pos * (placed_name * bool * metadata * type_hint option * expr option);
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
	mutable es_block_exprs:expr Queue.t;
	mutable es_exprs:expr Queue.t;
	mutable es_for_ctx:expr option list;
	mutable es_cfs:class_field Queue.t;
	mutable es_cc:class_constructor_t option list;
	mutable es_flags:int list;
	mutable es_uid:int;
	(*mutable es_ofs:class_field list;*)
	mutable es_cd:string * pos;
	mutable es_pkg:string list;
    mutable es_cname:placed_name;
}

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

let mk_static_new fn on p =
    let enew = ENew (({tparams=[];tsub=None;tname=on;tpackage=[]}, p), []), null_pos in
    {
        cff_name = (fn,p);
        cff_meta = [Meta.Val, [], p];
        cff_access = [APublic; AStatic];
        cff_doc = None;
        cff_kind = FProp(("default", p), ("never", p), None, Some enew) (*FVar (None, Some enew)*);
        cff_pos = null_pos;
    }

let to_pseudo_private cn fl =
	let tfr_field cf =
		if Meta.has Meta.Private cf.cff_meta then begin
			let ac = APrivate::(List.filter(fun c -> (c <> APrivate) && (c <> APublic)) cf.cff_access) in
			cf.cff_access <- ac;
			cf.cff_meta <- (Meta.Native, [mk_estring ("_" ^ (String.lowercase cn) ^ "_" ^ (fst cf.cff_name)) cf.cff_pos], cf.cff_pos)::cf.cff_meta;
		end
	in List.iter tfr_field fl

module Flag = struct
    let current_flag = ref 0

    let is_set f fs = (fs land f) <> 0
    let set f fs = fs lor f
    let clear f fs = (fs land (lnot f))

    let inside_cc_flag = 1
    let pop_expr_flag = 2
    let obj_decl_flag = 4
    let has_obj_decl_flag = 8

    let is_current_set f = is_set f !current_flag
    let set_current f = current_flag := (set f !current_flag)
    let clear_current f = current_flag := (clear f !current_flag)
end

module ObjectConstructor = struct
    let object_name = "HxObjects"
    let object_def_name = "@:object class"
    let object_prefix = "_"

    let mk_name name = object_prefix^name

    let unmk_name name =
        let l = String.length object_prefix in
        String.sub name l ((String.length name) - l)

    let get_function_meta meta pl al p =
        let meta =
            if pl=[] || not (Flag.is_current_set Flag.obj_decl_flag) then
                meta
            else
                (Meta.Generic, [], p)::meta
        in
        List.fold_left (fun acc ((n,_),_,meta,_,_) ->
		    List.fold_left (fun acc2 (sm,_,mp) ->
				match sm with
				| Meta.Implicit -> (Meta.ImplicitParam,[(EConst(Ident n),mp)],mp)::acc2
				| _ -> acc2
			) acc meta
		) meta al
end

module ExtState = struct
    open Tokenstream
    open Flag

    let mk_empty() = {es_block_exprs=Queue.create(); es_exprs=Queue.create(); es_for_ctx=[]; es_cfs=Queue.create(); es_cc=[]; es_flags=[]; es_uid=0; (*es_ofs=[];*) es_cd="",null_pos; es_pkg=[]; es_cname=("",null_pos)}

    let states = ref []

    let state = ref (mk_empty())

    let init_code:(expr Queue.t ref) = ref (Queue.create())

    let new_uid() =
        let id = (!state).es_uid + 1 in
        (!state).es_uid <- id;
        id

    let fresh_name pfx = pfx^(string_of_int (new_uid()))

    let save() =
        states := !state :: !states;
        state := mk_empty();
        current_flag := 0;
        ()

    let restore() =
        match !states with
        | x :: xs ->
            states := xs;
            state := x;
            let f =
                match x.es_flags with
                | i::is -> i
                | _ -> 0
            in current_flag := f
    | _ -> ()

    let push_flag f =
		(!state).es_flags <- (!current_flag)::(!state).es_flags;
		current_flag := f

    let pop_flag() = match (!state).es_flags with
        | x :: xs ->
            (!state).es_flags <- xs;
            let x =
                if is_current_set has_obj_decl_flag then Flag.set x has_obj_decl_flag
                else x
            in
            current_flag := x
        | _ -> current_flag := 0

    let set_and_push_flag f = push_flag (Flag.set f !current_flag)
    let clear_and_push_flag f = push_flag (Flag.clear f !current_flag)
    let is_current_flag_set f = Flag.is_set f !current_flag
    let set_current_flag f = current_flag := (Flag.set f !current_flag)
    let clear_current_flag f = current_flag := (Flag.clear f !current_flag)

    let insert_exprs ?(with_semi=true) (es:expr list) =
		let q = (!state).es_exprs in
		let insert e =
			Queue.push e q;
			if with_semi then insert_token [Semicolon, pos e]
		in
		List.iter insert es

    let insert_block_exprs ?(with_semi=true) (es:expr list) =
            let q = (!state).es_block_exprs in
            let insert e =
                Queue.push e q;
                if with_semi then insert_token [Semicolon, pos e]
            in
            List.iter insert es

    let is_expr_available() = not (Queue.is_empty (!state).es_exprs)
    let pop_expr() = Queue.pop (!state).es_exprs
    let pop_block_expr() = Queue.pop (!state).es_block_exprs

    let insert_cf (cf:class_field) = Queue.push cf (!state).es_cfs
    let is_cf_available() = not (Queue.is_empty (!state).es_cfs)
    let pop_cf() = Queue.pop (!state).es_cfs
    let pending_cfs acc =
        let q = (!state).es_cfs in
        let rec loop acc =
            if Queue.is_empty q then List.rev acc
            else loop ((Queue.pop q)::acc)
        in loop acc

    let mk_dotname ?(withClassName=false) n =
        let st = !state in
        let l =
            let cname = (fst st.es_cname) in
            if withClassName && (cname <> "") then
                cname::st.es_pkg
            else
                st.es_pkg
        in
        String.concat "." (List.rev (n::l))

    let add_object_def es n p =
        let cf = mk_static_new n (ObjectConstructor.mk_name n) p in
        set_current_flag has_obj_decl_flag;
        (*es.es_ofs <- cf::es.es_ofs;
        insert_cf cf;*)
        cf

    let add_classdecl n p =
        let es = !state in
        es.es_cd <- n,p;
        if is_current_set obj_decl_flag then Some(add_object_def es n p)
        else None

    let expr hx s =
        if is_expr_available() then
            pop_expr()
        else
            hx s

    let with_cc_do f =
        match (!state).es_cc with
        | (Some cc)::xs -> Some (f cc)
        | _ -> None

    let set_package pack s = (!state).es_pkg <- pack

    let set_cname cname s = (!state).es_cname <- cname
end

module ExtSymbol = struct
    let mk_empty() = {ss_can_access_local=true; ss_depth=0; ss_table=Hashtbl.create 0; ss_redeclared_names=[[]]; }

    let default = mk_empty()

    let all = ref default

    let set symbols = all := symbols

    let reset() = set default

    let update_from_cc occ =
	    all := match occ with
            | None -> default
            | Some cc -> cc.cc_symbols

    let add s cca = Hashtbl.add (!all.ss_table) s {s_name=s; s_redeclared_cnt=0; s_cca=cca; }
    let remove s = Hashtbl.remove (!all.ss_table) s

    let declared ns =
        if Flag.is_current_set Flag.inside_cc_flag then
            let ss = !all in
            let ht = ss.ss_table in
            let rec loop ns =
                match ns with
                | n::ns ->
                    begin try
                        let s = Hashtbl.find ht n in
                        if s.s_redeclared_cnt=0 then
                            let _,p,_ = s.s_cca.cca_arg in
                            !warning_ref ("Shadowing constructor parameter " ^ n) p;
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

    let undeclared pop_scope o_can_access_local =
        if Flag.is_current_set Flag.inside_cc_flag then
            let ss = !all in
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
        if Flag.is_current_set Flag.inside_cc_flag then
            let ss = !all in
            ss.ss_depth <- ss.ss_depth + 1;
            (match o_can_access_local with
            | Some b -> ss.ss_can_access_local <- b
            | _ -> ());
            ss.ss_redeclared_names <- ([])::ss.ss_redeclared_names

    let leave_scope o_can_access_local =
        undeclared true o_can_access_local

end

let dummy_cf = ("", null_pos), null_pos, FVar (None, None), [], None

let filter_class_fields fl =
	List.filter (fun cf -> match cf with {cff_name=("", _); _} -> false | _ -> true) fl

module ClassConstructor = struct
    open Ast
    open Globals
    open Flag
    open ExtState
    open ExtSymbol

    let init_code = ref (Queue.create())

    let push occ =
		(!state).es_cc <- occ::(!state).es_cc;
		match occ with
		| None ->
			ExtSymbol.reset();
			set_and_push_flag 0
		| Some cc ->
			ExtSymbol.set cc.cc_symbols;
			set_and_push_flag inside_cc_flag

    let pop() =
        let cc =
            match (!state).es_cc with
            | x::xs ->
                (!state).es_cc <- xs;
                update_from_cc x;
                x
            | _ ->
                update_from_cc None;
                None
        in
        pop_flag();
        cc

    let insert_expr cc e = Queue.push e cc.cc_code

    let insert_exprs el =
        let f cc =
            let q = cc.cc_code in
            List.iter (fun e -> Queue.push e q) el
        in with_cc_do f

    let add_arg_to_cf cca =
        if cca.cca_is_local then begin
            cca.cca_is_local <- false;
            let al, p, (name, opt, meta, ot, oe) = cca.cca_arg in
            ExtSymbol.remove (fst name);
            let t = type_or_infer ot in
            let meta, k =
                if cca.cca_is_mutable then
                    cca.cca_meta, FVar(t, None)
                else
                    (Meta.Val, [], p)::cca.cca_meta, FProp(("default", p), ("never", p), t, None)
            in
            let cf = {cff_name = name; cff_doc = None; cff_meta = (Meta.AllowWrite , [mk_eident (mk_dotname ~withClassName:true "new") p], p)(*::(Meta.AllowInitInCC, [], p)*)::meta; cff_access = al; cff_pos = p; cff_kind = k;} in
            Queue.push (mk_ethis_assign (fst name) p) !init_code;
            insert_cf cf
        end;
        cca

    let rec parse_opt_access ?(allow_inline=true) ?(allow_access=true) s = match s with parser
        | [< '(Kwd Private, _) when allow_access; s>] -> APrivate::(parse_opt_access ~allow_access:false ~allow_inline:allow_inline s)
        | [< '(Kwd Public, _) when allow_access; s>] -> APublic::(parse_opt_access ~allow_access:false ~allow_inline:allow_inline s)
        | [< '(Kwd Inline, _) when allow_inline; s >] -> AInline::(parse_opt_access  ~allow_access:allow_access ~allow_inline:false s)
        | [< >] -> if allow_access then [APublic] else []

    let parse_param_opt_access = parser
        | [< '(Kwd Private, _) >] -> [APrivate]
        | [< '(Kwd Public, _) >] -> [APublic]
        | [< >] -> [APublic]

    let parse_param_opt_modifier = parser
        | [< '(Kwd Var, _) >] -> false, true
        | [< '(Kwd Val, _) >] -> false, false
        | [< >] -> true, false

    let parse_param_with_ac meta ac (il, im) s =
        let is_opt = match s with parser
            | [< '(Question,_) >] -> true
            | [< >] -> false
        in
        match s with parser
        | [< name, pn=(!dollar_ident_ref); t=(!parse_type_opt_ref); c=(!parse_fun_param_value_ref) >] ->
            let meta = if il then (Meta.Private, [], pn)::meta else meta in
            let arg = {cca_arg=(ac, pn, ((name, pn), is_opt, [], t, c)); cca_meta=meta; cca_is_local=true; cca_is_mutable=im; } in
            if il then begin
                ExtSymbol.add name arg;
                arg
            end
            else add_arg_to_cf arg

    let parse_param = parser
        | [< meta=(!parse_meta_ref); ac=parse_param_opt_access; m=parse_param_opt_modifier; s >] -> parse_param_with_ac meta ac m s

    let parse_extends occ s = match occ with
        | Some cc ->
            (match s with parser
                | [< '(POpen, p1); s >] ->
                    let super = (mk_eident "super" p1) in
                    let _ = match s with parser
                        | [< super_call = (!parse_call_params_ref) (fun el p2 -> (ECall(super, el)), punion p1 p2) p1 >] ->
                            insert_expr cc super_call
                    in ()
                | [< >] -> ())
        | _ -> ()

    let mk_fun ?(is_inlined=false) ?(ignore_cp=false) fun_name cc p1 p2 =
        let mk_arg = function
            | {cca_arg=(_, _, cf_arg); _} -> cf_arg
        in
        let init = List.rev (Queue.fold (fun a e -> e::a) [] cc.cc_code) in
        let args = List.map mk_arg cc.cc_args in
        let al = if is_inlined then AInline::cc.cc_al else cc.cc_al in
        let cp = if ignore_cp then [] else cc.cc_constraints in
        mk_cff_fun fun_name cc.cc_meta al cp args (EBlock init) p1 p2

    let mk_f ?(ignore_cp=false) p cc =
        let mk_arg = function
            | {cca_arg=(_, _, (n, b, _, ot, oe)); _} -> (n,b,[],ot,oe)
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

    let mk_init_field n e p =
        let e = mk_eassign (mk_eident n p) e in
        let _ = insert_exprs [e] in ()

    let mk_delayed_init is_cc name e t p =
        if is_cc then begin
            (match e with
            | Some e -> mk_init_field (fst name) e (snd name)
            | _ -> ());
            None, type_or_infer t, p
        end else e, t, p

    let parse_code metas failed semicolon s =
        try
            match s with parser
            | [< e = (!expr_ref); s >] ->
                semicolon s;
                let _ = insert_exprs [attach_meta_to_expr metas e] in
                dummy_cf
            | [< '(Semicolon,p) >] -> dummy_cf
            | [< >] -> failed()
        with Display e ->
            let e = attach_meta_to_expr metas e in
            let _ = insert_exprs [e] in
            match with_cc_do (mk_f ~ignore_cp:true (pos e)) with
            | None -> dummy_cf
            | Some f -> ("new", pos e), pos e, FFun f, [], None


    let parse meta class_flags cname cp p custom_error s =
        set_cname cname s;
        if (class_flags=[]) && (has_meta Meta.Object meta) then
            set_and_push_flag obj_decl_flag;

        let mk_data() =
            let ss = ExtSymbol.mk_empty() in
                let ic = Queue.create() in
                    ExtSymbol.set ss;
                    init_code := ic;
                    ss, ic
        in
        let mk_cc meta acl arl cp (ss, ic) =
            Some {cc_meta=meta; cc_al=acl; cc_args=arl; cc_symbols=ss; cc_code=(!init_code); cc_constraints=cp; }
        in
        let cc = match s with parser
            | [< meta=(!parse_meta_ref); acl=parse_opt_access; s >] ->
                (match s with parser
                    | [< '(POpen,o1); s >] ->
                        let data = mk_data() in (
                        match s with parser
                            | [< arl=psep Comma parse_param ; '(PClose,o2) >] -> mk_cc meta acl arl cp data
                        )
                    | [< >] -> None
                )
            | [< >] -> None
        in
        let cc =
            if is_current_set obj_decl_flag then
                (*let aname = mk_dotname ObjectConstructor.object_name in*)
                match cc with
                | Some c ->
                    if cp<>[] then custom_error ("No constraint parameter allowed in "^ObjectConstructor.object_def_name^" declaration") p;
                    if c.cc_args<>[] then custom_error ("No parameters allowed in "^ObjectConstructor.object_def_name^" constructor") p;
                    let acl = APrivate::AInline::(List.filter(fun a -> a<>APublic) c.cc_al) in
                    let meta = (* (Meta.Allow,[mk_eident aname p],p):: *)c.cc_meta in
                    Some {c with cc_meta=meta; cc_al=acl; }
                | _ ->
                    mk_cc [(* (Meta.Allow,[mk_eident aname p],p) *)] [APrivate; AInline] [] [] (mk_data())
            else cc
        in
        push cc;
        cc

    let rec update_cfs occ fl p1 p2 = match occ with
        | Some cc ->
            if not (List.exists (fun cf -> match cf with {cff_name=("new", _); cff_kind=FFun _; _} -> true | _ -> false) fl) then begin
                (mk_fun ~ignore_cp:true ("new",p1) cc p1 p2)::fl
            end else
                fl
        | _ -> fl

    and get_class_info (name, pname) class_field dflags meta p1 p2 =
        let odf = is_current_set obj_decl_flag in
        let name, dflags, meta =
            if odf then
                let name = ObjectConstructor.mk_name name in
                let meta = (Meta.Final, [], pname)::meta in
                let dflags =
                    ExtState.pop_flag();
					(*HPrivate::*)dflags
                in name, dflags, meta
            else name, dflags, meta
        in
        let cc = pop() in
        let class_field = update_cfs cc class_field p1 p2 in
        to_pseudo_private name class_field;
        let meta = match cc with
            | None -> meta
            | _ -> (Meta.PublicFields, [], p1)::meta

		in
        (name, pname), class_field, dflags, meta
end

let reserved_kwd_allowed = parser
	| [< '(Kwd Val, p) >] -> "val", p
	| [< '(Kwd Def,p) >] -> "def", p

let const_pos s = match Stream.npeek 2 s with
	| [Kwd Val, p; t] ->
		(match fst t with
		| Kwd In | Kwd Else -> None
		| POpen | Const(Ident _) | Kwd _ -> Some p
		| _ -> None)
	| _ -> None

let parse_const_expr s =
	let sp = const_pos s in
	match  sp with
	| Some p ->
		Stream.junk s;
		EVars [(!parse_var_decl_ref) ~is_const:true s], p
	| None ->
		let n, p = reserved_kwd_allowed s in
		(!expr_next_ref) (mk_eident n p) s

let parse_consts_expr s =
	let sp = const_pos s in
	match  sp with
	| Some p ->
		Stream.junk s;
		(!parse_var_decls_ref) ~is_const:true p s, p
	| None -> raise Stream.Failure


let add_cc_arg_to_cf cca =
	if cca.cca_is_local then begin
		cca.cca_is_local <- false;
		let al, p, (name, opt, meta, ot, oe) = cca.cca_arg in
		ExtSymbol.remove (fst name);
		let t = type_or_infer ot in
		let meta,k =
			if cca.cca_is_mutable then cca.cca_meta, FVar(t, None)
			else (Meta.Val, [], p)::cca.cca_meta, FProp(("default",p), ("never",p), t, None)
		in
		let cf = {cff_name = name; cff_doc = None; cff_meta = (Meta.AllowWrite , [mk_eident (ExtState.mk_dotname ~withClassName:true "new") p], p)::(*(Meta.AllowInitInCC, [], p)::*)cca.cca_meta; cff_access = al; cff_pos = p; cff_kind = k;} in
		Queue.push (mk_ethis_assign (fst name) (snd name)) !ExtState.init_code;
		ExtState.insert_cf cf
	end;
	cca

let use_symbol n =
    if Flag.is_current_set Flag.inside_cc_flag then
        try
            let ss = !ExtSymbol.all in
            let no_local = not ss.ss_can_access_local in
            let s = Hashtbl.find ss.ss_table n in
            if no_local && s.s_redeclared_cnt=0 then
                let _ = add_cc_arg_to_cf s.s_cca in ()
        with Not_found -> ()
    else ()

let use_expr e =
	if Flag.is_current_set Flag.inside_cc_flag then
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
	if Flag.is_current_set Flag.inside_cc_flag then
		match e with
		| EVars vs , _ ->
			ExtSymbol.declared (List.map (fun ((n, _) ,_,_) -> n) vs);
			e
		| _ -> e
	else e

let add_parsed_const ?(junk=true) meta s =
	let sp = const_pos s in
	match  sp with
	| Some p ->
		if junk then Stream.junk s;
		(mk_metaval p)::meta, sp
	| None -> meta, sp

let  parse_opt_class_body p1 name s =
	let _ = ExtState.add_classdecl (fst name) (snd name) in
    match s with parser
		| [< '(Semicolon,p) >] -> ExtState.pending_cfs [], p
		| [< '(BrOpen,_); fl, p2 = (!parse_class_fields_ref) false p1 >] ->
			fl, p2

let add_const_init al e =
	let al = List.filter (fun (_,_,m,_,_) -> Meta.has Meta.Val m) al in
	match al with
	| [] -> e
	| _ ->
		let p = pos e in
		let al = List.map (fun (n,_,_,_,_) -> mk_efield (mk_eident (fst n) p) "__to_val__" p) al in
		match e with
		| EBlock b, pb -> mk_eblock (al@b) pb
		| _ -> mk_eblock (al@[e]) p

let is_static_allowed() = not (Flag.is_current_set Flag.obj_decl_flag)

let is_function_allowed name p1 custom_error s =
	if Flag.is_current_set Flag.obj_decl_flag then
		match name with
		| "new" ->
			custom_error ("No constructor allowed in "^ObjectConstructor.object_def_name^" declaration") p1;
			false
		| _ -> true
	else true

let parse_opt_fun_args s =
	match Stream.peek s with
		| Some(Binop OpLt, _)  | Some(POpen, _) ->
			(match s with parser
			| [< pl = (!parse_constraint_params_ref); '(POpen,_); al = psep Comma (!parse_fun_param_ref); '(PClose,_) >] ->
				Some (pl, al)
            )
		| _ -> None

let augment_decls pack decls =
    let es = !ExtState.state in

    if Flag.is_current_set Flag.has_obj_decl_flag then begin
        Flag.clear_current Flag.has_obj_decl_flag;
        let p = (snd es.es_cd) in
        let fn = get_filename p.pfile in
        let mk_import name p =
            let pname = pack@[fn; name; name] in
		    let pname = List.map(fun n -> n,p) pname in
            (EImport (pname, INormal), null_pos)
        in
        let extra_imports = ref [] in
        let decls =
            let is_object_decl ec = has_meta Meta.Object ec.d_meta in
            let rec partition part1 part2 lst =
                match lst with
                | [] ->  part1, part2
                | x::xs ->
                    (match x with
                    | EClass ec, p ->
                        if is_object_decl ec then
                            partition ((ec,p)::part1) part2 xs
                        else
                            partition part1 ((ec,p)::part2) xs
                    | _ -> partition part1 part2 xs
                    )
            in
            let decls = List.rev decls in
            let odecls, cdecls = partition [] [] decls in
            let rec remap acc os =
                match os with
                | [] -> acc
                | (ec,p) as x::(_ as xs) ->
                    let pname = snd ec.d_name in
                    let oname = fst ec.d_name in
                    let name = ObjectConstructor.unmk_name oname in
                    extra_imports := (mk_import name pname)::!extra_imports;
                    try
                        let x = List.find (fun (ec, _) -> name=(fst ec.d_name)) cdecls in
                        let ec,p = x in
                        let meta = (Meta.HasObjectSingleton,[],pname)::(Meta.Access,[mk_eident (ExtState.mk_dotname oname) pname],pname)::ec.d_meta in
                        let data = (mk_static_new name oname pname)::ec.d_data in
                        remap ((x, ({ec with d_meta=meta; d_data=data; }, p))::acc) xs
                    with Not_found ->
                        let meta = (Meta.HasObjectSingleton,[],pname)::ec.d_meta in
                        let data = (mk_static_new name name pname)::ec.d_data in
                        remap ((x, ({ ec with d_meta=meta; d_name=(name, pname); d_data=data; }, p))::acc) xs
            in
            let ndecls = remap [] odecls in
            let ndecls =
                let rec remap acc nd od =
                    match nd, od with
                    | [], [] -> acc
                    | [], x::(_ as xs) -> remap (x::acc) nd xs
                    | ((oec, op), (xec, xp))::(_ as xs), y::(_ as ys) ->
                        (match y with
                        | EClass yec, yp when yec=oec && yp=op -> remap ((EClass xec, xp)::acc) xs ys
                        | _ -> remap (y::acc) nd ys
                        )
                in remap [] ndecls decls
            in
            (!extra_imports)@ndecls
        in
        pack, decls
	end else
		pack, decls

let mk_true p = EConst (Ident "true"),p

let mk_false p = EConst (Ident "false"),p

let mk_cast e ot p = ECast(e, ot), p

let mk_assign e1 e2 = EBinop(OpAssign, e1, e2), punion (pos e1) (pos e2)

let rewrite_if cond e1 e2 p =
    let vars = ref [] in
    let map e =
        match e with
        | ECall((EField((EConst(Ident "Std"), _),"is"),p_is),[e1;(EMeta((Meta.Rtti, [ECast ((EConst(Ident vn),pv) as v, ((Some (CTPath t,pt)) as oct) ) , _], _), (e2)), _)]), p when not(e1==v) ->
            let asg = mk_assign v (mk_cast e1 None p) in
            let asg = EParenthesis(EBlock[asg; mk_true p], p), p in
            vars := (EVars[((vn,pv), oct, None)], p)::!vars;
            (EParenthesis(EBinop (OpBoolAnd, e, asg), p), p) 
        | _ -> e
    in 
    let cond = Ast.map_expr map cond in
    let eif = EIf (cond,e1,e2), p in
    if !vars=[] then eif        
    else
        let bk = [eif] in
        let bk = List.rev_append !vars bk in
        EBlock bk, p