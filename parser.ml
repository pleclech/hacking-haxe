(*
 * Copyright (C)2005-2013 Haxe Foundation
 *
 * Permission is hereby granted, free of charge, to any person obtaining a
 * copy of this software and associated documentation files (the "Software"),
 * to deal in the Software without restriction, including without limitation
 * the rights to use, copy, modify, merge, publish, distribute, sublicense,
 * and/or sell copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
 * DEALINGS IN THE SOFTWARE.
 *)

open Ast

type error_msg =
	| Unexpected of token
	| Duplicate_default
	| Missing_semicolon
	| Unclosed_macro
	| Unimplemented
	| Missing_type
	| Custom of string

exception Error of error_msg * pos
exception TypePath of string list * (string * bool) option * bool (* in import *)
exception Display of expr
exception ContinueClassField of expr * token
exception BreakBlock

let error_msg = function
	| Unexpected t -> "Unexpected "^(s_token t)
	| Duplicate_default -> "Duplicate default"
	| Missing_semicolon -> "Missing ;"
	| Unclosed_macro -> "Unclosed macro"
	| Unimplemented -> "Not implemented for current platform"
	| Missing_type -> "Missing type declaration"
	| Custom s -> s

let error m p = raise (Error (m,p))
let display_error : (error_msg -> pos -> unit) ref = ref (fun _ _ -> assert false)

let quoted_ident_prefix = "@$__hx__"

let quote_ident s =
	quoted_ident_prefix ^ s

let unquote_ident f =
	let pf = quoted_ident_prefix in
	let pflen = String.length pf in
	let is_quoted = String.length f >= pflen && String.sub f 0 pflen = pf in
	let s = if is_quoted then String.sub f pflen (String.length f - pflen) else f in
	let is_valid = not is_quoted || try
		for i = 0 to String.length s - 1 do
			match String.unsafe_get s i with
			| 'a'..'z' | 'A'..'Z' | '_' -> ()
			| '0'..'9' when i > 0 -> ()
			| _ -> raise Exit
		done;
		if Hashtbl.mem Lexer.keywords s then raise Exit;
		true
	with Exit ->
		false
	in
	s,is_quoted,is_valid

let cache = ref (DynArray.create())
let last_doc = ref None
let use_doc = ref false
let use_parser_resume = ref true
let resume_display = ref null_pos
let in_macro = ref false

let last_token s =
	let n = Stream.count s in
	DynArray.get (!cache) (if n = 0 then 0 else n - 1)

let serror() = raise (Stream.Error "")

let do_resume() = !resume_display <> null_pos

let display e = raise (Display e)

let type_path sl in_import = match sl with
	| n :: l when n.[0] >= 'A' && n.[0] <= 'Z' -> raise (TypePath (List.rev l,Some (n,false),in_import));
	| _ -> raise (TypePath (List.rev sl,None,in_import))

let is_resuming p =
	let p2 = !resume_display in
	p.pmax = p2.pmin && !use_parser_resume && Common.unique_full_path p.pfile = p2.pfile

let set_resume p =
	resume_display := { p with pfile = Common.unique_full_path p.pfile }

let is_dollar_ident e = match fst e with
	| EConst (Ident n) when n.[0] = '$' ->
		true
	| _ ->
		false

let precedence op =
	let left = true and right = false in
	match op with
	| OpMod -> 0, left
	| OpMult | OpDiv -> 1, left
	| OpAdd | OpSub -> 2, left
	| OpShl | OpShr | OpUShr -> 3, left
	| OpOr | OpAnd | OpXor -> 4, left
	| OpEq | OpNotEq | OpGt | OpLt | OpGte | OpLte -> 5, left
	| OpInterval -> 6, left
	| OpBoolAnd -> 7, left
	| OpBoolOr -> 8, left
	| OpArrow -> 9, right
	| OpAssign | OpAssignOp _ -> 10, right

let is_not_assign = function
	| OpAssign | OpAssignOp _ -> false
	| _ -> true

let swap op1 op2 =
	let p1, left1 = precedence op1 in
	let p2, _ = precedence op2 in
	left1 && p1 <= p2

let rec make_binop op e ((v,p2) as e2) =
	match v with
	| EBinop (_op,_e,_e2) when swap op _op ->
		let _e = make_binop op e _e in
		EBinop (_op,_e,_e2) , punion (pos _e) (pos _e2)
	| ETernary (e1,e2,e3) when is_not_assign op ->
		let e = make_binop op e e1 in
		ETernary (e,e2,e3) , punion (pos e) (pos e3)
	| _ ->
		EBinop (op,e,e2) , punion (pos e) (pos e2)

let rec make_unop op ((v,p2) as e) p1 =
	match v with
	| EBinop (bop,e,e2) -> EBinop (bop, make_unop op e p1 , e2) , (punion p1 p2)
	| ETernary (e1,e2,e3) -> ETernary (make_unop op e1 p1 , e2, e3), punion p1 p2
	| _ ->
		EUnop (op,Prefix,e), punion p1 p2

let rec make_meta name params ((v,p2) as e) p1 =
	match v with
	| EBinop (bop,e,e2) -> EBinop (bop, make_meta name params e p1 , e2) , (punion p1 p2)
	| ETernary (e1,e2,e3) -> ETernary (make_meta name params e1 p1 , e2, e3), punion p1 p2
	| _ ->
		EMeta((name,params,p1),e),punion p1 p2

(* vv extended syntax vv *)
let use_extended_syntax = ref false

let out_of_order_exprs:expr list ref = ref []
let out_of_order_cfs:class_field list ref = ref []

let for_ctx = ref []

let push_for_ctx a = for_ctx := a :: !for_ctx

let pop_for_ctx() = match !for_ctx with
	| [] -> ()
	| x::xs -> for_ctx := xs

let peek_for_ctx() = match !for_ctx with
	| [] -> None
	| x::xs -> x

let warning : (string -> pos -> unit) ref = ref (fun _ _ -> assert false)

(* for debugging purpose *)
let dump_n_token n s =
		if !use_extended_syntax then
		let p = ref null_pos in
		match Stream.npeek n s with
			| [] -> ()
			| x::xs ->
				let m=List.map(fun (t,p2) -> p:=punion !p p2; ("< " ^ (s_token t) ^ " >")) (x::xs) in
				!warning (String.concat " " m) !p

let var_id = ref 0

let mk_fresh_name ?(sfx="") pfx =
		let i = !var_id in
		var_id := i + 1;
		pfx ^ (string_of_int i) ^ sfx

let struct_var_name_prefix = "__st"

let struct_global_var_marker = "$st$"

let flags_stack = ref []
let current_flag = ref 0

let noDbldotFlag = 1
let parseOptTypeFlag = 2
let fieldsDeclarationFlag = 4
let ccDefinedFlag = 8
let hasLocalAccessFlag = 16
let initInCCFlag = 32
let discardPossibleClassFieldMemberFlag = 64

let s_flag f =
	let is f v = (f land v)<>0 in
	let cl f v = f land (lnot v) in
	let rec loop acc f =
		if is f noDbldotFlag then loop ("noDbldotFlag"::acc) (cl f noDbldotFlag)
		else if is f parseOptTypeFlag then loop ("parseOptTypeFlag"::acc) (cl f parseOptTypeFlag)
		else if is f fieldsDeclarationFlag then loop ("fieldsDeclarationFlag"::acc) (cl f fieldsDeclarationFlag)
		else if is f ccDefinedFlag then loop ("ccDefinedFlag"::acc) (cl f ccDefinedFlag)
		else if is f hasLocalAccessFlag then loop ("hasLocalAccessFlag"::acc) (cl f hasLocalAccessFlag)
		else if is f initInCCFlag then loop ("initInCCFlag"::acc) (cl f initInCCFlag)
		else if is f discardPossibleClassFieldMemberFlag then loop ("discardPossibleClassFieldMemberFlag"::acc) (cl f discardPossibleClassFieldMemberFlag)
		else acc
	in 
	let acc = loop [] f in
	String.concat "|" acc

let get_flag() = !current_flag 

let is_flag_set f = (!current_flag land f)<>0

let set_flag f = current_flag := !current_flag lor f

let clear_flag f = current_flag := !current_flag land (lnot f)

let push_flag f = set_flag f; flags_stack := !current_flag::!flags_stack

let push_not_flag f = clear_flag f; flags_stack := !current_flag::!flags_stack

let pop_flag() = 
	let f = match !flags_stack with
	| [] -> 0
	| x::xs -> flags_stack := xs; x
	in
	current_flag := f;
	f


type destructure_name = string * pos
type destructure_elm = {
	mutable name: string * string;
	mutable globals_def: (destructure_name * destructure_name * expr) list;
	mutable globals:  (destructure_name * destructure_name) list;
	mutable locals: (destructure_name * destructure_name) list;
	mutable protected: bool;
	mutable structures: destructure_elm list;
}

let mk_structure_elm n = {name=n; globals_def=[]; globals=[]; locals=[]; structures=[]; protected=false;}

let mk_ident n p = (EConst(Ident n), p)
let mk_string n p = (EConst(String n), p)

type cc_arg_mode =
	| Read
	| Write

type scope_def_from =
	| SDFClass of string
	| SDFFunction of string
	| SDFOther

type field_type =
	| NormalField
	| LocalField
	| PrivateField

let s_from = function
	| SDFClass s -> "class "^s
	| SDFFunction s -> "function "^s
	| SDFOther -> "other"

type 'a def_value =  {ht:(string , 'a) Hashtbl.t; parent:'a def_node; from:scope_def_from;mutable exprs:expr list}
and 'a def_node = Nil | DefValue of 'a def_value

type cc_arg = {
	mutable arg: access list * pos * (string * bool * complex_type option * expr option);
	is_mutable : bool;
	mutable mode : field_type;
	mutable use_cnt: int;
	mutable meta: metadata;
}

type cc_field_def = {
	ccfd_access: access list;
	ccfd_meta: metadata;
	ccfd_mutable: bool;
}

type cc_param = {
	cc_open_par : pos;
	cc_close_par : pos;
	cc_params : type_param list;
	cc_args : cc_arg list;
	cc_access : access list;
}

type cc_info = {
	mutable cc_param : cc_param option;
	mutable cc_super_args : pos * expr list option;
}
let cc_arg_defs:'a def_value list ref = ref []
let cl_sym_defs:'a def_value list ref  = ref []

let mk_def_value p f = {ht=Hashtbl.create 0; parent=p; from=f; exprs=[];}

let get_def_parent = function
	| [] -> Nil
	| x::xs -> DefValue x

let leave_scope s = if !use_extended_syntax then
	match !s with
	| [] -> ()
	| x::xs -> s:=xs

let push s e = s:=e::!s

let enter_scope s f = if !use_extended_syntax then
	push s (mk_def_value (get_def_parent !s) f)

let is_cc_scope = function
	| {parent=Nil;from=_ as f; _} ->
		(match f with 
		| SDFClass _ -> true
		| _ -> false)
	| _ -> false

let find_in_scope ?(deep=true) s n =
	if !use_extended_syntax then
		if not deep then 
			match !s with
			| [] -> None
			| x::xs -> 
				try Some(Hashtbl.find x.ht n)
				with Not_found -> None
		else
			let rec loop = function
				| [] -> None
				| x::xs -> 
					try Some(Hashtbl.find x.ht n) 
					with Not_found -> loop xs
			in loop !s
	else None

let get_scope_for ?(deep=true) s n =
	if !use_extended_syntax then
		if not deep then 
			match !s with
			| [] -> None
			| x::xs -> 
				try
					Hashtbl.find x.ht n;
					Some(x)
				with Not_found -> None
		else
			let rec loop = function
				| [] -> None
				| x::xs -> 
					try 
						Hashtbl.find x.ht n;
						Some(x)
					with Not_found -> loop xs
			in loop !s
	else None

let mk_this p = mk_ident "this" p

let mk_this_assign fn pfn =
	let e_this = mk_this pfn in
	let e_this = (EField (e_this, fn) , pfn) in
	make_binop OpAssign e_this (mk_ident fn pfn)

let mk_call fn fa pfn =	ECall (mk_ident fn pfn, fa), pfn

let mk_int i p = EConst (Int i), p

let parse_cc_opt_access = parser
	| [< '(Kwd Private, _) >] -> [APrivate]
	| [< '(Kwd Public, _) >] -> [APublic]
	| [< >] -> [APublic]

let parse_cc_param_opt_access = parser
	| [< '(Kwd Private, _) >] -> [APrivate]
	| [< '(Kwd Public, _) >] -> [APublic]
	| [< >] -> [APublic]

let parse_cc_param_opt_modifier = parser
	| [< '(Kwd Var, _) >] -> NormalField, true
	| [< '(Kwd KConst, _) >] -> NormalField, false
	| [< >] -> LocalField, false

let get_opt_name = function
	| None -> "", null_pos
	| Some(n, p) -> n, p

let mk_local_private v =
	if v.mode=LocalField then begin
		v.mode <- PrivateField;
		let al, p, r = v.arg in
		let al = List.filter(fun a -> a<>APublic && a<>APrivate) al in
		let l = List.length al in
		(*print_string ("mk private:"^(string_of_int l)^"\n");*)
		v.meta <- (Meta.Private, [], p) :: v.meta;
		v.arg <- (APrivate::al), p, r
	end

let add_cl_sym_def ?(new_scope:scope_def_from option=None) ?(field_def:cc_field_def option=None) s p = 
	if !use_extended_syntax && not !in_macro then
		let shadowing v pos opt_adder =
			let tp = match v.arg with
				| _,p,_ -> p
			in
			let printer file line = Printf.sprintf "%d:" line in
			let tp = Lexer.get_error_pos printer tp in
			if (v.use_cnt=0 && v.mode=LocalField) then begin
				!warning (s ^ " is shadowing constructor parameter declared at " ^ tp)  pos;
				match opt_adder with
				| Some(adder) -> adder()
				| _ -> ()
			end else begin
				mk_local_private v;
				error (Custom (s ^ " is overriding constructor parameter declared at " ^ tp)) pos
			end
		in
		match field_def with
		| None ->
				let scope = cl_sym_defs in
				let _ = match !scope with 
				| [] -> ()
				| x::xs when s<>"" ->
					(*println("try to add '"^s^" into "^(s_from x.from));*)
					let add() = Hashtbl.add x.ht s p; in
					if is_cc_scope x then begin
						(*println("add_cl_sym_def:"^s);*)
						let cf = find_in_scope cc_arg_defs s ~deep:false in
						match cf with
						| Some v ->
							if not (v.mode=LocalField) then
								let tp = match v.arg with
								| _,p,_ -> p
								in
								let printer file line = Printf.sprintf "%d:" line in
								let tp = Lexer.get_error_pos printer tp in
								error (Custom ("can't redeclared constructor parameter " ^ s ^ " declared at " ^ tp)) p
							else
								shadowing v p (Some add)
						| None -> add()
					end else
						let cf = find_in_scope cc_arg_defs s ~deep:false in
						(match cf with
						| Some v ->
								let tp = match v.arg with
								| _,p,_ -> p
								in
								let printer file line = Printf.sprintf "%d:" line in
								let tp = Lexer.get_error_pos printer tp in
								!warning (s ^ " is shadowing constructor parameter declared at " ^ tp)  p;
								add()
						| None -> add())
				| _ -> ()
				in
				(match new_scope with
				| Some f -> enter_scope scope f
				| _ -> ())
		| Some {ccfd_access=_ as al; ccfd_mutable=_ as im; ccfd_meta=_ as meta} ->
			let cf = find_in_scope cc_arg_defs s ~deep:false in
			let add v = match !cc_arg_defs with x::xs -> (*println("adding in class field '"^s^" into "^(s_from x.from));*) Hashtbl.add x.ht s v | _ -> () in
			(match cf with
			| Some v ->
				mk_local_private v;
				shadowing v p None
			| None -> add {arg=al, p ,(s, false, None, None);is_mutable=im;mode=NormalField;use_cnt=0;meta=meta;})

let exists_in_scope ?(deep=true) s n =
	if (!use_extended_syntax) then
		if not deep then 
			match !s with
			| [] -> false
			| x::xs -> Hashtbl.mem x.ht n
		else
			let rec loop = function
				| [] -> false
				| x::xs -> 
					if Hashtbl.mem x.ht n then true 
					else loop xs
			in loop !s
	else false

let use_def ?(check_scope=true) has_local_access s =
	if (!use_extended_syntax && not !in_macro) then
		let sv = if check_scope then find_in_scope cl_sym_defs s else None in
		let cv = find_in_scope cc_arg_defs ~deep:false s in
	(*print_string (s ^ " : " ^ (string_of_bool check_scope) ^ " , " ^ (string_of_bool has_local_access) ^ "\n");*)
		let incr = match cv with
			| Some cf ->
				set_flag initInCCFlag;
				(*print_string ("find in cc arg " ^ s ^ "[" ^ (s_flag !current_flag) ^ "\n");*)
				if not has_local_access then begin
					mk_local_private cf;
					cf.use_cnt <- cf.use_cnt + 1;
				end
			| _ -> ()
		in
		match sv with
	    	| None -> incr
	    	| Some _ -> set_flag initInCCFlag

let use_cc_arg s m = 
	if (!use_extended_syntax && not !in_macro) then
		match !cc_arg_defs with
			| [] -> ()
			| x::xs ->
				try
					let cf = Hashtbl.find x.ht s in
					let v = get_scope_for cl_sym_defs s
					in match v with 
					| None -> ()
					| Some(v) when is_cc_scope v ->
						(match m with
						| Read -> cf.use_cnt <- cf.use_cnt + 1
						| Write ->
							if (cf.is_mutable) then 
								cf.use_cnt <- cf.use_cnt + 1
							else
								match cf.arg with
								| _, p , (n, _, _, _) -> error (Custom ("can't write into immutable argument " ^ n)) p)
					| _ -> ()
				with Not_found -> ()

let mk_type pack name params sub =
	{
		tpackage = List.rev pack;
		tname = name;
		tparams = params;
		tsub = sub;
	}

let mk_type_inf pack =
	mk_type pack "Dynamic" ([TPType(CTPath {tpackage=[];tname="_";tparams=[];tsub=None;})]) None

let mk_cc_fields fields =
	let mk_field = function
		| {arg=ac, p, (n, _, t, e); is_mutable=_ as im; meta=_ as m; _} ->
			let t =
				if t=None then Some(CTPath (mk_type_inf []))
				else t
			in
			let k = 
				if (im) then FVar(t, e)
				else FProp("default", "never", t, e)
			in
			{
				cff_name = n;
				cff_doc = None;
				cff_meta = [(Meta.AllowWrite , [mk_ident "new" p], p)] @ m;
				cff_access = ac;
				cff_pos = p;
				cff_kind = k;
			}
	in
	List.map mk_field fields


let mk_cc_init cc p1 p2 =
    let filter_field = function
    	| {mode=_ as m; _} -> m<>LocalField
    in
	let fields =
		match cc with
      	| {cc_param=Some {cc_args=_ as ca; _}; _} -> ca
      	| _ -> []
    in
    let fields = List.filter filter_field fields in
    	let sp, cc_super_args, callsuper = match cc.cc_super_args with
    	| p, None -> p, [], false
    	| p, Some xs -> p, xs, true
    	in
		let super_idents = List.filter(function | EConst(Ident _), _ -> true | _ -> false) cc_super_args in
		(match cc.cc_param with
		| None -> 
			(match super_idents with
			| [] -> ()
			| (EConst(Ident n), p1)::xs -> error (Custom ("undefined parameter " ^ n) ) p1
			| _ -> ())
		| Some(cp) ->
			let exists_ident n = function
				| {arg=(_, _ , (n1, _, _, _)); _} when (n1=n) -> true
				| _ -> false
			in
			let check_ident = function
				| EConst(Ident n), p1  when n<>"null"-> if (not (List.exists (exists_ident n) cp.cc_args)) then error (Custom ("undefined parameter " ^ n) ) p1
				| _ -> ()
			in
			List.iter check_ident super_idents
		);
		let super =
			if not callsuper then []
			else let super = mk_call "super" cc_super_args sp in [super]
		in
		let mk_assign = function
		| {arg=(_, p, (n, _, _, _)); _} -> mk_this_assign n p
		in
		let assigns = match cc.cc_param with
			| None -> []
			| Some(cp) -> (List.map mk_assign fields)
		in
		let code = 
			match !cc_arg_defs with
			| x::_ -> 
				(*println("fields.len:"^string_of_int(List.length x.exprs));*)
				let rec loop acc fields = match fields with
				| [] -> acc
				| y::ys ->
					let i = List.length ys in
				 	(*let call = mk_call ("if" ^ (string_of_int i)) [] null_pos in
					loop (y::call::acc) ys *)
					loop (y::acc) ys
				in
				let exprs = x.exprs in
				x.exprs <- [];
				loop [] exprs
			| _ -> []
		in
		let init = super @ List.rev_append assigns code
		in
		let fields = mk_cc_fields fields in
		let mk_new ac cp args p1 p2 = 
			let f =  
				{
					f_params = cp;
					f_args = args;
					f_type = None;
					f_expr = Some(EBlock init, p2);
				} 
			in
				{
					cff_name = "new";
					cff_doc = None;
					cff_meta = [];
					cff_access = ac;
					cff_pos = punion p1 p2;
					cff_kind = FFun f;
				}
			in
			match cc.cc_param with
			| None -> if (init == []) then fields else fields @ [mk_new [APublic] [] [] p1 p2]
			| Some(cp) ->
				let mk_arg = function
					| {arg=(_, _, a); _} -> a
				in 
				let args = List.map mk_arg cp.cc_args in
				List.rev_append fields [mk_new cp.cc_access cp.cc_params args cp.cc_open_par cp.cc_close_par]
	
let add_cc_to_fields cc p1 p2 fl =
	if (!use_extended_syntax) then
		(mk_cc_init cc p1 p2) @ fl
	else fl

(* ^^ extended syntax ^^ *)

let reify in_macro =
	let cur_pos = ref None in
	let mk_enum ename n vl p =
		let constr = (EConst (Ident n),p) in
		match vl with
		| [] -> constr
		| _ -> (ECall (constr,vl),p)
	in
	let to_const c p =
		let cst n v = mk_enum "Constant" n [EConst (String v),p] p in
		match c with
		| Int i -> cst "CInt" i
		| String s -> cst "CString" s
		| Float s -> cst "CFloat" s
		| Ident s -> cst "CIdent" s
		| Regexp (r,o) -> mk_enum "Constant" "CRegexp" [(EConst (String r),p);(EConst (String o),p)] p
	in
	let rec to_binop o p =
		let op n = mk_enum "Binop" n [] p in
		match o with
		| OpAdd -> op "OpAdd"
		| OpMult -> op "OpMult"
		| OpDiv -> op "OpDiv"
		| OpSub -> op "OpSub"
		| OpAssign -> op "OpAssign"
		| OpEq -> op "OpEq"
		| OpNotEq -> op "OpNotEq"
		| OpGt -> op "OpGt"
		| OpGte -> op "OpGte"
		| OpLt -> op "OpLt"
		| OpLte -> op "OpLte"
		| OpAnd -> op "OpAnd"
		| OpOr -> op "OpOr"
		| OpXor -> op "OpXor"
		| OpBoolAnd -> op "OpBoolAnd"
		| OpBoolOr -> op "OpBoolOr"
		| OpShl -> op "OpShl"
		| OpShr -> op "OpShr"
		| OpUShr -> op "OpUShr"
		| OpMod -> op "OpMod"
		| OpAssignOp o -> mk_enum "Binop" "OpAssignOp" [to_binop o p] p
		| OpInterval -> op "OpInterval"
		| OpArrow -> op "OpArrow"
	in
	let to_string s p =
		let len = String.length s in
		if len > 1 && s.[0] = '$' then
			(EConst (Ident (String.sub s 1 (len - 1))),p)
		else
			(EConst (String s),p)
	in
	let to_array f a p =
		(EArrayDecl (List.map (fun s -> f s p) a),p)
	in
	let to_null p =
		(EConst (Ident "null"),p)
	in
	let to_opt f v p =
		match v with
		| None -> to_null p
		| Some v -> f v p
	in
	let to_bool o p =
		(EConst (Ident (if o then "true" else "false")),p)
	in
	let to_obj fields p =
		(EObjectDecl fields,p)
	in
	let rec to_tparam t p =
		let n, v = (match t with
			| TPType t -> "TPType", to_ctype t p
			| TPExpr e -> "TPExpr", to_expr e p
		) in
		mk_enum "TypeParam" n [v] p
	and to_tpath t p =
		let len = String.length t.tname in
		if t.tpackage = [] && len > 1 && t.tname.[0] = '$' then
			(EConst (Ident (String.sub t.tname 1 (len - 1))),p)
		else begin
			let fields = [
				("pack", to_array to_string t.tpackage p);
				("name", to_string t.tname p);
				("params", to_array to_tparam t.tparams p);
			] in
			to_obj (match t.tsub with None -> fields | Some s -> fields @ ["sub",to_string s p]) p
		end
	and to_ctype t p =
		let ct n vl = mk_enum "ComplexType" n vl p in
		match t with
		| CTPath { tpackage = []; tparams = []; tsub = None; tname = n } when n.[0] = '$' ->
			to_string n p
		| CTPath t -> ct "TPath" [to_tpath t p]
		| CTFunction (args,ret) -> ct "TFunction" [to_array to_ctype args p; to_ctype ret p]
		| CTAnonymous fields -> ct "TAnonymous" [to_array to_cfield fields p]
		| CTParent t -> ct "TParent" [to_ctype t p]
		| CTExtend (tl,fields) -> ct "TExtend" [to_array to_tpath tl p; to_array to_cfield fields p]
		| CTOptional t -> ct "TOptional" [to_ctype t p]
	and to_fun f p =
		let farg (n,o,t,e) p =
			let fields = [
				"name", to_string n p;
				"opt", to_bool o p;
				"type", to_opt to_ctype t p;
			] in
			to_obj (match e with None -> fields | Some e -> fields @ ["value",to_expr e p]) p
		in
		let rec fparam t p =
			let fields = [
				"name", to_string t.tp_name p;
				"constraints", to_array to_ctype t.tp_constraints p;
				"params", to_array fparam t.tp_params p;
			] in
			to_obj fields p
		in
		let fields = [
			("args",to_array farg f.f_args p);
			("ret",to_opt to_ctype f.f_type p);
			("expr",to_opt to_expr f.f_expr p);
			("params",to_array fparam f.f_params p);
		] in
		to_obj fields p
	and to_cfield f p =
		let p = f.cff_pos in
		let to_access a p =
			let n = (match a with
			| APublic -> "APublic"
			| APrivate -> "APrivate"
			| AStatic -> "AStatic"
			| AOverride -> "AOverride"
			| ADynamic -> "ADynamic"
			| AInline -> "AInline"
			| AMacro -> "AMacro"
			) in
			mk_enum "Access" n [] p
		in
		let to_kind k =
			let n, vl = (match k with
				| FVar (ct,e) -> "FVar", [to_opt to_ctype ct p;to_opt to_expr e p]
				| FFun f -> "FFun", [to_fun f p]
				| FProp (get,set,t,e) -> "FProp", [to_string get p; to_string set p; to_opt to_ctype t p; to_opt to_expr e p]
			) in
			mk_enum "FieldType" n vl p
		in
		let fields = [
			Some ("name", to_string f.cff_name p);
			(match f.cff_doc with None -> None | Some s -> Some ("doc", to_string s p));
			(match f.cff_access with [] -> None | l -> Some ("access", to_array to_access l p));
			Some ("kind", to_kind f.cff_kind);
			Some ("pos", to_pos f.cff_pos);
			(match f.cff_meta with [] -> None | l -> Some ("meta", to_meta f.cff_meta p));
		] in
		let fields = List.rev (List.fold_left (fun acc v -> match v with None -> acc | Some e -> e :: acc) [] fields) in
		to_obj fields p
	and to_meta m p =
		to_array (fun (m,el,p) _ ->
			let fields = [
				"name", to_string (fst (Common.MetaInfo.to_string m)) p;
				"params", to_expr_array el p;
				"pos", to_pos p;
			] in
			to_obj fields p
		) m p
	and to_pos p =
		match !cur_pos with
		| Some p ->
			p
		| None ->
		let file = (EConst (String p.pfile),p) in
		let pmin = (EConst (Int (string_of_int p.pmin)),p) in
		let pmax = (EConst (Int (string_of_int p.pmax)),p) in
		if in_macro then
			(EUntyped (ECall ((EConst (Ident "__dollar__mk_pos"),p),[file;pmin;pmax]),p),p)
		else
			to_obj [("file",file);("min",pmin);("max",pmax)] p
	and to_expr_array a p = match a with
		| [EMeta ((Meta.Dollar "a",[],_),e1),_] -> (match fst e1 with EArrayDecl el -> to_expr_array el p | _ -> e1)
		| _ -> to_array to_expr a p
	and to_expr e _ =
		let p = snd e in
		let expr n vl =
			let e = mk_enum "ExprDef" n vl p in
			to_obj [("expr",e);("pos",to_pos p)] p
		in
		let loop e = to_expr e (snd e) in
		match fst e with
		| EConst (Ident n) when n.[0] = '$' && String.length n > 1 ->
			to_string n p
		| EConst c ->
			expr "EConst" [to_const c p]
		| EArray (e1,e2) ->
			expr "EArray" [loop e1;loop e2]
		| EBinop (op,e1,e2) ->
			expr "EBinop" [to_binop op p; loop e1; loop e2]
		| EField (e,s) ->
			expr "EField" [loop e; to_string s p]
		| EParenthesis e ->
			expr "EParenthesis" [loop e]
		| EObjectDecl fl ->
			expr "EObjectDecl" [to_array (fun (f,e) -> to_obj [("field",to_string f p);("expr",loop e)]) fl p]
		| EArrayDecl el ->
			expr "EArrayDecl" [to_expr_array el p]
		| ECall (e,el) ->
			expr "ECall" [loop e;to_expr_array el p]
		| ENew (t,el) ->
			expr "ENew" [to_tpath t p;to_expr_array el p]
		| EUnop (op,flag,e) ->
			let op = mk_enum "Unop" (match op with
				| Increment -> "OpIncrement"
				| Decrement -> "OpDecrement"
				| Not -> "OpNot"
				| Neg -> "OpNeg"
				| NegBits -> "OpNegBits"
			) [] p in
			expr "EUnop" [op;to_bool (flag = Postfix) p;loop e]
		| EVars vl ->
			expr "EVars" [to_array (fun (v,t,e,m) p ->
				let fields = [
					"name", to_string v p;
					"type", to_opt to_ctype t p;
					"expr", to_opt to_expr e p;
				] in
				to_obj fields p
			) vl p]
		| EFunction (name,f) ->
			let name = match name with
				| None ->
					to_null p
				| Some name ->
					if ExtString.String.starts_with name "inline_$" then begin
						let real_name = (String.sub name 7 (String.length name - 7)) in
						let e_name = to_string real_name p in
						let e_inline = to_string "inline_" p in
						let e_add = (EBinop(OpAdd,e_inline,e_name),p) in
						e_add
					end else
						to_string name p
			in
			expr "EFunction" [name; to_fun f p]
		| EBlock el ->
			expr "EBlock" [to_expr_array el p]
		| EFor (e1,e2) ->
			expr "EFor" [loop e1;loop e2]
		| EIn (e1,e2) ->
			expr "EIn" [loop e1;loop e2]
		| EIf (e1,e2,eelse) ->
			expr "EIf" [loop e1;loop e2;to_opt to_expr eelse p]
		| EWhile (e1,e2,flag) ->
			expr "EWhile" [loop e1;loop e2;to_bool (flag = NormalWhile) p]
		| ESwitch (e1,cases,def) ->
			let scase (el,eg,e) p =
				to_obj [("values",to_expr_array el p);"guard",to_opt to_expr eg p;"expr",to_opt to_expr e p] p
			in
			expr "ESwitch" [loop e1;to_array scase cases p;to_opt (to_opt to_expr) def p]
		| ETry (e1,catches) ->
			let scatch (n,t,e) p =
				to_obj [("name",to_string n p);("type",to_ctype t p);("expr",loop e)] p
			in
			expr "ETry" [loop e1;to_array scatch catches p]
		| EReturn eo ->
			expr "EReturn" [to_opt to_expr eo p]
		| EBreak ->
			expr "EBreak" []
		| EContinue ->
			expr "EContinue" []
		| EUntyped e ->
			expr "EUntyped" [loop e]
		| EThrow e ->
			expr "EThrow" [loop e]
		| ECast (e,ct) ->
			expr "ECast" [loop e; to_opt to_ctype ct p]
		| EDisplay (e,flag) ->
			expr "EDisplay" [loop e; to_bool flag p]
		| EDisplayNew t ->
			expr "EDisplayNew" [to_tpath t p]
		| ETernary (e1,e2,e3) ->
			expr "ETernary" [loop e1;loop e2;loop e3]
		| ECheckType (e1,ct) ->
			expr "ECheckType" [loop e1; to_ctype ct p]
		| EMeta ((m,ml,p),e1) ->
			match m, ml with
			| Meta.Dollar ("" | "e"), _ ->
				e1
			| Meta.Dollar "a", _ ->
				expr "EArrayDecl" (match fst e1 with EArrayDecl el -> [to_expr_array el p] | _ -> [e1])
			| Meta.Dollar "b", _ ->
				expr "EBlock" [e1]
			(* TODO: can $v and $i be implemented better? *)
			| Meta.Dollar "v", _ ->
				begin match fst e1 with
				| EParenthesis (ECheckType (e2, CTPath{tname="String";tpackage=[]}),_) -> expr "EConst" [mk_enum "Constant" "CString" [e2] (pos e2)]
				| EParenthesis (ECheckType (e2, CTPath{tname="Int";tpackage=[]}),_) -> expr "EConst" [mk_enum "Constant" "CInt" [e2] (pos e2)]
				| EParenthesis (ECheckType (e2, CTPath{tname="Float";tpackage=[]}),_) -> expr "EConst" [mk_enum "Constant" "CFloat" [e2] (pos e2)]
				| _ -> (ECall ((EField ((EField ((EField ((EConst (Ident "haxe"),p),"macro"),p),"Context"),p),"makeExpr"),p),[e; to_pos (pos e)]),p)
				end
			| Meta.Dollar "i", _ ->
				expr "EConst" [mk_enum "Constant" "CIdent" [e1] (pos e1)]
			| Meta.Dollar "p", _ ->
				(ECall ((EField ((EField ((EField ((EConst (Ident "haxe"),p),"macro"),p),"MacroStringTools"),p),"toFieldExpr"),p),[e]),p)
			| Meta.Custom ":pos", [pexpr] ->
				let old = !cur_pos in
				cur_pos := Some pexpr;
				let e = loop e1 in
				cur_pos := old;
				e
			| _ ->
				expr "EMeta" [to_obj [("name",to_string (fst (Common.MetaInfo.to_string m)) p);("params",to_expr_array ml p);("pos",to_pos p)] p;loop e1]
	and to_tparam_decl p t =
		to_obj [
			"name", to_string t.tp_name p;
			"params", (EArrayDecl (List.map (to_tparam_decl p) t.tp_params),p);
			"constraints", (EArrayDecl (List.map (fun t -> to_ctype t p) t.tp_constraints),p)
		] p
	and to_type_def (t,p) =
		match t with
		| EClass d ->
			let ext = ref None and impl = ref [] and interf = ref false in
			List.iter (function
				| HExtern | HPrivate -> ()
				| HInterface -> interf := true;
				| HExtends t -> ext := Some (to_tpath t p)
				| HImplements i -> impl := (to_tpath i p) :: !impl
			) d.d_flags;
			to_obj [
				"pack", (EArrayDecl [],p);
				"name", to_string d.d_name p;
				"pos", to_pos p;
				"meta", to_meta d.d_meta p;
				"params", (EArrayDecl (List.map (to_tparam_decl p) d.d_params),p);
				"isExtern", to_bool (List.mem HExtern d.d_flags) p;
				"kind", mk_enum "TypeDefKind" "TDClass" [(match !ext with None -> (EConst (Ident "null"),p) | Some t -> t);(EArrayDecl (List.rev !impl),p);to_bool !interf p] p;
				"fields", (EArrayDecl (List.map (fun f -> to_cfield f p) d.d_data),p)
			] p
		| _ -> assert false
	in
	(fun e -> to_expr e (snd e)), to_ctype, to_type_def

let popt f = parser
	| [< v = f >] -> Some v
	| [< >] -> None

let rec plist f = parser
	| [< v = f; l = plist f >] -> v :: l
	| [< >] -> []

let rec psep sep f = parser
	| [< v = f; s >] ->
		let rec loop = parser
			| [< '(sep2,_) when sep2 = sep; v = f; l = loop >] -> v :: l
			| [< >] -> []
		in
		v :: loop s
	| [< >] -> []

let opt_ident s =
	let l = String.length s in
	if l=0 then false, ""
	else 
		if (String.get s 0)='?' then true, String.sub s 1 (l-1)
		else  false, s

let allow_kwd_or_else allow_kwd fn s =
	if allow_kwd then
		match s with parser
			| [< '(Kwd KConst, p) >] -> "const", p
			| [< '(Kwd Def, p) >] -> "def", p
			| [< i,p = fn >] -> i,p
	else
		match s with parser
			| [< i,p = fn >] -> i,p

let ident ?(allow_kwd=false) s =
	let hx s = match s with parser
		| [< '(Const (Ident i),p) >] -> i,p
	in
	allow_kwd_or_else allow_kwd hx s


let ident_or_const s =
	match Stream.npeek 2 s with
	| [(Kwd KConst, _); (Const (Ident _), _)] -> ident s
	| [(Kwd KConst, _); (Kwd _, _)] -> ident s
	| [(Kwd KConst, p); _] ->
		Stream.junk s;
		"const", p
	| [(Kwd Def, _); (Const (Ident _), _)] -> ident s
	| [(Kwd Def, _); (Kwd _, _)] -> ident s
	| [(Kwd Def, p); _] ->
		Stream.junk s;
		"def", p
	| _ -> ident s

let dollar_ident ?(allow_kwd=false) s = 
	let hx s = match s with parser
	| [< '(Const (Ident i),p) >] -> i,p
	| [< '(Dollar i,p) >] -> ("$" ^ i),p
	in
	allow_kwd_or_else allow_kwd hx s

let dollar_ident_or_const ?(allow_kwd=false) s =
	if allow_kwd then
		dollar_ident ~allow_kwd:allow_kwd s
	else
		match Stream.npeek 2 s with
		| [(Kwd KConst, _); (Const (Ident _), _)] ->
			dollar_ident s
		| [(Kwd KConst, _); (Kwd _, _)] ->
			dollar_ident s
		| [(Kwd KConst, p); _] ->
			Stream.junk s;
			"const", p
		| [(Kwd Def, _); (Const (Ident _), _)] ->
			dollar_ident s
		| [(Kwd Def, _); (Kwd  _, _)] ->
			dollar_ident s
		| [(Kwd Def, p); _] ->
			Stream.junk s;
			"def", p
		| _ -> dollar_ident s

let dollar_ident_macro pack = parser
	| [< '(Const (Ident i),p) >] -> i,p
	| [< '(Dollar i,p) >] -> ("$" ^ i),p
	| [< '(Kwd Macro,p) when pack <> [] >] -> "macro", p
	| [< '(Kwd Extern,p) when pack <> [] >] -> "extern", p

let lower_ident_or_macro = parser
	| [< '(Const (Ident i),p) when is_lower_ident i >] -> i
	| [< '(Kwd Macro,_) >] -> "macro"
	| [< '(Kwd Extern,_) >] -> "extern"

let any_enum_ident = parser
	| [< i = ident >] -> i
	| [< '(Kwd k,p) when Filename.basename p.pfile = "StdTypes.hx" >] -> s_keyword k, p

let property_ident = parser
	| [< i, _ = ident >] -> i
	| [< '(Kwd Dynamic,_) >] -> "dynamic"
	| [< '(Kwd Default,_) >] -> "default"
	| [< '(Kwd Null,_) >] -> "null"

let get_doc s =
	(* do the peek first to make sure we fetch the doc *)
	match Stream.peek s with
	| None -> None
	| Some (tk,p) ->
		match !last_doc with
		| None -> None
		| Some (d,pos) ->
			last_doc := None;
			if pos = p.pmin then Some d else None

let comma = parser
	| [< '(Comma,_) >] -> ()

let semicolon s =
	if fst (last_token s) = BrClose then
		match s with parser
		| [< '(Semicolon,p) >] -> p
		| [< >] -> snd (last_token s)
	else
		match s with parser
		| [< '(Semicolon,p) >] -> p
		| [< s >] ->
			let pos = snd (last_token s) in
			if do_resume() then pos else error Missing_semicolon pos

let rec	parse_file s =
	last_doc := None;
	match s with parser
	| [< '(Kwd Package,_); pack = parse_package; s >] ->
		begin match s with parser
		| [< '(Const(Ident _),p) when pack = [] >] -> error (Custom "Package name must start with a lowercase character") p
		| [< _ = semicolon; l = parse_type_decls pack []; '(Eof,_) >] -> pack , l
		end
	| [< l = parse_type_decls [] []; '(Eof,_) >] -> [] , l

and parse_type_decls pack acc s =
	try
		match s with parser
		| [< v = parse_type_decl; l = parse_type_decls pack (v :: acc) >] -> l
		| [< >] -> List.rev acc
	with TypePath ([],Some (name,false),b) ->
		(* resolve imports *)
		List.iter (fun d ->
			match fst d with
			| EImport (t,_) ->
				(match List.rev t with
				| (n,_) :: path when n = name && List.for_all (fun (i,_) -> is_lower_ident i) path -> raise (TypePath (List.map fst (List.rev path),Some (name,false),b))
				| _ -> ())
			| _ -> ()
		) acc;
		raise (TypePath (pack,Some(name,true),b))

and parse_opt_class_body p1 =
	if (!use_extended_syntax) then begin
		push_flag fieldsDeclarationFlag;
		let e = parser
		| [< '(Semicolon,p) >] -> [], p
		| [< '(BrOpen,_); fl, p2 = parse_class_fields false p1 >] ->
			let allow_init cf = cf.cff_meta <- (Meta.AllowInitInCC,[],null_pos) :: cf.cff_meta in
			List.iter (fun c -> match c with | {cff_kind=FVar _; } as cf -> allow_init cf | {cff_kind=FProp _; } as cf -> allow_init cf | _ -> ()) fl;
			fl, p2
		in
		let _=pop_flag() in
		e
	end else parser
		| [< '(BrOpen,_); fl, p2 = parse_class_fields false p1 >] -> fl, p2

and to_pseudo_private cn fl =
	let tfr_field cf =
		if Meta.has Meta.Private cf.cff_meta then begin
			let ac = APrivate::(List.filter(fun c -> (c<>APrivate)&&(c<>APublic)) cf.cff_access) in
			cf.cff_access <- ac;
			cf.cff_meta <- (Meta.Native, [mk_string ("_"^(String.lowercase cn)^"_"^cf.cff_name) cf.cff_pos], cf.cff_pos)::cf.cff_meta;
		end
	in List.iter tfr_field fl;

and parse_type_decl s =
	match s with parser
	| [< '(Kwd Import,p1) >] -> parse_import s p1
	| [< '(Kwd Using,p1); t = parse_type_path; p2 = semicolon >] -> EUsing t, punion p1 p2
	| [< doc = get_doc; meta = parse_meta; c = parse_common_flags; s >] ->
		match s with parser
		| [< n , p1 = parse_enum_flags; name = type_name; tl = parse_constraint_params; '(BrOpen,_); l = plist parse_enum; '(BrClose,p2) >] ->
			(EEnum {
				d_name = name;
				d_doc = doc;
				d_meta = meta;
				d_params = tl;
				d_flags = List.map snd c @ n;
				d_data = l
			}, punion p1 p2)
		| [< n , p1 = parse_class_flags; name = type_name; tl = parse_constraint_params; cc=parse_class_constructor name; hl = plist (parse_class_herit ~cc:cc); fl, p2 = parse_opt_class_body p1 >] ->
			let fl = add_cc_to_fields cc p1 p2 fl in
			to_pseudo_private name fl;
			(*print_string ((String.concat "\n" (List.map (fun e -> s_field e) fl)) ^ "\n");*)
			let _ = if is_flag_set ccDefinedFlag then pop_flag() else 0 in
			leave_scope cl_sym_defs;
			leave_scope cc_arg_defs;
			(EClass {
				d_name = name;
				d_doc = doc;
				d_meta = meta;
				d_params = tl;
				d_flags = List.map fst c @ n @ hl;
				d_data = fl;
			}, punion p1 p2)
		| [< '(Kwd Typedef,p1); name = type_name; tl = parse_constraint_params; '(Binop OpAssign,p2); t = parse_complex_type; s >] ->
			(match s with parser
			| [< '(Semicolon,_) >] -> ()
			| [< >] -> ());
			(ETypedef {
				d_name = name;
				d_doc = doc;
				d_meta = meta;
				d_params = tl;
				d_flags = List.map snd c;
				d_data = t;
			}, punion p1 p2)
		| [< '(Kwd Abstract,p1); name = type_name; tl = parse_constraint_params; st = parse_abstract_subtype; sl = plist parse_abstract_relations; '(BrOpen,_); fl, p2 = parse_class_fields false p1 >] ->
			let flags = List.map (fun (_,c) -> match c with EPrivate -> APrivAbstract | EExtern -> error (Custom "extern abstract not allowed") p1) c in
			let flags = (match st with None -> flags | Some t -> AIsType t :: flags) in
			(EAbstract {
				d_name = name;
				d_doc = doc;
				d_meta = meta;
				d_params = tl;
				d_flags = flags @ sl;
				d_data = fl;
			},punion p1 p2)

and parse_class doc meta cflags need_name s =
	let opt_name = if need_name then type_name else (fun s -> match popt type_name s with None -> "" | Some n -> n) in
	match s with parser
	| [< n , p1 = parse_class_flags; name = opt_name; tl = parse_constraint_params; hl = psep Comma parse_class_herit; '(BrOpen,_); fl, p2 = parse_class_fields (not need_name) p1 >] ->
		(EClass {
			d_name = name;
			d_doc = doc;
			d_meta = meta;
			d_params = tl;
			d_flags = List.map fst cflags @ n @ hl;
			d_data = fl;
		}, punion p1 p2)

and parse_import s p1 =
	let rec loop acc =
		match s with parser
		| [< '(Dot,p) >] ->
			let resume() =
				type_path (List.map fst acc) true
			in
			if is_resuming p then resume();
			(match s with parser
			| [< '(Const (Ident k),p) >] ->
				loop ((k,p) :: acc)
			| [< '(Kwd Macro,p) >] ->
				loop (("macro",p) :: acc)
			| [< '(Kwd Extern,p) >] ->
				loop (("extern",p) :: acc)
			| [< '(Binop OpMult,_); '(Semicolon,p2) >] ->
				p2, List.rev acc, IAll
			| [< '(Binop OpOr,_) when do_resume() >] ->
				set_resume p;
				resume()
			| [< >] ->
				serror());
		| [< '(Semicolon,p2) >] ->
			p2, List.rev acc, INormal
		| [< '(Kwd In,_); '(Const (Ident name),_); '(Semicolon,p2) >] ->
			p2, List.rev acc, IAsName name
		| [< '(Const (Ident "as"),_); '(Const (Ident name),_); '(Semicolon,p2) >] ->
			p2, List.rev acc, IAsName name
		| [< >] ->
			serror()
	in
	let p2, path, mode = (match s with parser
		| [< '(Const (Ident name),p) >] -> loop [name,p]
		| [< >] -> serror()
	) in
	(EImport (path,mode),punion p1 p2)

and parse_abstract_relations s =
	match s with parser
	| [< '(Const (Ident "to"),_); t = parse_complex_type >] -> AToType t
	| [< '(Const (Ident "from"),_); t = parse_complex_type >] -> AFromType t

and parse_abstract_subtype s =
	match s with parser
	| [< '(POpen, _); t = parse_complex_type; '(PClose,_) >] -> Some t
	| [< >] -> None

and parse_package s = psep Dot lower_ident_or_macro s

and parse_class_fields tdecl p1 s =
	let l = parse_class_field_resume tdecl s in
	let p2 = (match s with parser
		| [< '(BrClose,p2) >] -> p2
		| [< >] -> if do_resume() then p1 else serror()
	) in
	l, p2

and empty_ffun = FFun {
		f_params = [];
		f_args = [];
		f_type = None;
		f_expr = None;
	}

and parse_class_field_resume tdecl s =
	if not (do_resume()) then
		if (!use_extended_syntax) then
			let pcf s =
				try
					parse_class_field s
				with 
					| ContinueClassField(e, t) ->
						let ci, i = match !cc_arg_defs with
							| x::xs -> let i=List.length x.exprs in x,i
							| _ -> serror()
						in
						(*let fn = EFunction(Some("inline_if" ^ string_of_int i), {f_params=[];f_args=[];f_type=None;f_expr=Some(e,p);}), p in*)
						ci.exprs <- e::ci.exprs;
						let n = match t with
							| BrClose -> "}"
							| _ -> ""
						in {
							cff_name = n;
							cff_doc = None;
							cff_meta = [];
							cff_access = [];
							cff_pos = null_pos;
							cff_kind = empty_ffun;
						}
			in
			let rec loop acc s = match s with parser
				| [< v = pcf; s >] -> 
					(match v.cff_name with
					| "}" -> acc
					| "" -> loop acc s
					| _ -> loop (v::acc) s)
				| [< >] -> acc
			in
			loop [] s
		else
			plist parse_class_field s
	else try
		if (!use_extended_syntax) then
			let pcf s =
				try
					parse_class_field s
				with 
					| ContinueClassField(e, t) ->
						let ci, i = match !cc_arg_defs with
							| x::xs -> let i=List.length x.exprs in x,i
							| _ -> serror()
						in
						(*let fn = EFunction(Some("inline_if" ^ string_of_int i), {f_params=[];f_args=[];f_type=None;f_expr=Some(e,p);}), p in*)
						ci.exprs <- e::ci.exprs;
						let n = match t with
							| BrClose -> "}"
							| _ -> ""
						in {
							cff_name = n;
							cff_doc = None;
							cff_meta = [];
							cff_access = [];
							cff_pos = null_pos;
							cff_kind = empty_ffun;
						}
			in
			let rec loop acc s = match s with parser
				| [< v = pcf; s >] -> 
					(match v.cff_name with
					| "}" -> acc
					| "" -> loop acc s
					| _ -> loop (v::acc) s)
				| [< >] -> acc
			in
			loop [] s
		else
			let c = parse_class_field s in
			c :: parse_class_field_resume tdecl s
	with 
		| Stream.Error _ | Stream.Failure ->
		(* look for next variable/function or next type declaration *)
		let rec junk k =
			if k <= 0 then () else begin
				Stream.junk s;
				junk (k - 1);
			end
		in
		(*
			walk back tokens which are prefixing a type/field declaration
		*)
		let rec junk_tokens k =
			if k = 0 then
				()
			else match List.rev_map fst (Stream.npeek k s) with
			| Kwd Private :: _ -> junk_tokens (k - 1)
			| (Const (Ident _) | Kwd _) :: DblDot :: At :: l
			| (Const (Ident _) | Kwd _) :: At :: l ->
				junk_tokens (List.length l)
			| PClose :: l ->
				(* count matching parenthesises for metadata call *)
				let rec loop n = function
					| [] -> []
					| POpen :: l -> if n = 0 then l else loop (n - 1) l
					| PClose :: l -> loop (n + 1) l
					| _ :: l -> loop n l
				in
				(match loop 0 l with
				| (Const (Ident _) | Kwd _) :: At :: l
				| (Const (Ident _) | Kwd _) :: DblDot :: At :: l -> junk_tokens (List.length l)
				| _ ->
					junk k)
			| _ ->
				junk k
		in
		let rec loop k =
			match List.rev_map fst (Stream.npeek k s) with
			(* metadata *)
			| Kwd _ :: At :: _ | Kwd _ :: DblDot :: At :: _ ->
				loop (k + 1)
			(* field declaration *)
			| Const _ :: Kwd Function :: _
			| Kwd New :: Kwd Function :: _ ->
				junk_tokens (k - 2);
				parse_class_field_resume tdecl s
			| Kwd Macro :: _ | Kwd Public :: _ | Kwd Static :: _ | Kwd Var :: _ | Kwd KConst :: _| Kwd Def :: _ | Kwd Override :: _ | Kwd Dynamic :: _ | Kwd Inline :: _ ->
				junk_tokens (k - 1);
				parse_class_field_resume tdecl s
			| BrClose :: _ when tdecl ->
				junk_tokens (k - 1);
				[]
			(* type declaration *)
			| Eof :: _ | Kwd Import :: _ | Kwd Using :: _ | Kwd Extern :: _ | Kwd Class :: _ | Kwd Interface :: _ | Kwd Enum :: _ | Kwd Typedef :: _ | Kwd Abstract :: _->
				junk_tokens (k - 1);
				[]
			| [] ->
				[]
			| _ ->
				loop (k + 1)
		in
		loop 1

and parse_common_flags = parser
	| [< '(Kwd Private,_); l = parse_common_flags >] -> (HPrivate, EPrivate) :: l
	| [< '(Kwd Extern,_); l = parse_common_flags >] -> (HExtern, EExtern) :: l
	| [< >] -> []

and parse_meta_argument_expr s =
	try
		expr s
	with Display e -> match fst e with
		| EDisplay(e,_) ->
			begin try
				type_path (string_list_of_expr_path_raise e) false
			with Exit ->
				e
			end
		| _ ->
			e

and parse_meta_params pname s = match s with parser
	| [< '(POpen,p) when p.pmin = pname.pmax; params = psep Comma parse_meta_argument_expr; '(PClose,_); >] -> params
	| [< >] -> []

and parse_meta_entry = parser
	[< '(At,_); name,p = meta_name; params = parse_meta_params p; s >] -> (name,params,p)

and parse_meta = parser
	| [< entry = parse_meta_entry; s >] ->
		entry :: parse_meta s
	| [< >] -> []

and meta_name = parser
	| [< '(Const (Ident i),p) >] -> (Meta.Custom i), p
	| [< '(Kwd k,p) >] -> (Meta.Custom (s_keyword k)),p
	| [< '(DblDot,_); s >] -> match s with parser
		| [< '(Const (Ident i),p) >] -> (Common.MetaInfo.parse i), p
		| [< '(Kwd k,p) >] -> (Common.MetaInfo.parse (s_keyword k)),p

and parse_enum_flags = parser
	| [< '(Kwd Enum,p) >] -> [] , p

and parse_class_flags = parser
	| [< '(Kwd Class,p) >] -> [] , p
	| [< '(Kwd Interface,p) >] -> [HInterface] , p

and parse_type_hint = parser
	| [< '(DblDot,_); t = parse_complex_type >] -> t

and parse_type_opt = parser
	| [< t = parse_type_hint >] -> Some t
	| [< >] -> None

and parse_complex_type s =
	let t = parse_complex_type_inner s in
	parse_complex_type_next t s

and parse_structural_extension = parser
	| [< '(Binop OpGt,_); t = parse_type_path; '(Comma,_); s >] ->
		t

and parse_complex_type_inner = parser
	| [< '(POpen,_); t = parse_complex_type; '(PClose,_) >] -> CTParent t
	| [< '(BrOpen,p1); s >] ->
		(match s with parser
		| [< l = parse_type_anonymous false >] -> CTAnonymous l
		| [< t = parse_structural_extension; s>] ->
			let tl = t :: plist parse_structural_extension s in
			(match s with parser
			| [< l = parse_type_anonymous false >] -> CTExtend (tl,l)
			| [< l, _ = parse_class_fields true p1 >] -> CTExtend (tl,l))
		| [< l, _ = parse_class_fields true p1 >] -> CTAnonymous l
		| [< >] -> serror())
	| [< '(Question,_); t = parse_complex_type_inner >] ->
		CTOptional t
	| [< t = parse_type_path >] ->
		CTPath t

and parse_type_path s = parse_type_path1 [] s

and parse_type_path1 pack = parser
	| [< name, p = dollar_ident_macro pack; s >] ->
		if (is_lower_ident name) && (name <> "_") then
			(match s with parser
			| [< '(Dot,p) >] ->
				if is_resuming p then
					raise (TypePath (List.rev (name :: pack),None,false))
				else
					parse_type_path1 (name :: pack) s
			| [< '(Semicolon,_) >] ->
				error (Custom "Type name should start with an uppercase letter") p
			| [< >] -> serror())
		else
			let name,params,sub =
				if (name="_") then
					"Dynamic", [TPType(CTPath {tpackage=[];tname="_";tparams=[];tsub=None;})], None
				else
					let sub = (match s with parser
						| [< '(Dot,p); s >] ->
							(if is_resuming p then
								raise (TypePath (List.rev pack,Some (name,false),false))
							else match s with parser
								| [< '(Const (Ident name),_) when not (is_lower_ident name) >] -> Some name
								| [< '(Binop OpOr,_) when do_resume() >] ->
									set_resume p;
									raise (TypePath (List.rev pack,Some (name,false),false))
								| [< >] -> serror())
						| [< >] -> None
					) in
					let params = (match s with parser
						| [< '(Binop OpLt,_); l = psep Comma parse_type_path_or_const; '(Binop OpGt,_) >] -> l
						| [< >] -> []
					) in
					let ln = (List.length params) in
					let sub =
						match name, sub with
						| "Tuple", None when ln > 1 ->
							Some(name^(string_of_int ln))
						| _ ->
							sub
					in
					name, params, sub
			in mk_type pack name params sub
	| [< '(Binop OpOr,_) when do_resume() >] ->
		raise (TypePath (List.rev pack,None,false))

and type_name = parser
	| [< '(Const (Ident name),p) >] ->
		if is_lower_ident name then
			error (Custom "Type name should start with an uppercase letter") p
		else
			name
	| [< '(Dollar name,_) >] -> "$" ^ name

and parse_type_path_or_const = parser
	(* we can't allow (expr) here *)
	| [< '(BkOpen,p1); l = parse_array_decl; '(BkClose,p2); s >] -> TPExpr (EArrayDecl l, punion p1 p2)
	| [< t = parse_complex_type >] -> TPType t
	| [< '(Const c,p) >] -> TPExpr (EConst c,p)
	| [< e = expr >] -> TPExpr e
	| [< >] -> serror()

and parse_complex_type_next t = parser
	| [< '(Arrow,_); t2 = parse_complex_type >] ->
		(match t2 with
		| CTFunction (args,r) ->
			CTFunction (t :: args,r)
		| _ ->
			CTFunction ([t] , t2))
	| [< >] -> t

and parse_type_anonymous opt = parser
	| [< '(Question,_) when not opt; s >] -> parse_type_anonymous true s
	| [< name, p1 = ident; t = parse_type_hint; s >] ->
		let next p2 acc =
			{
				cff_name = name;
				cff_meta = if opt then [Meta.Optional,[],p1] else [];
				cff_access = [];
				cff_doc = None;
				cff_kind = FVar (Some t,None);
				cff_pos = punion p1 p2;
			} :: acc
		in
		match s with parser
		| [< '(BrClose,p2) >] -> next p2 []
		| [< '(Comma,p2) >] ->
			(match s with parser
			| [< '(BrClose,_) >] -> next p2 []
			| [< l = parse_type_anonymous false >] -> next p2 l
			| [< >] -> serror());
		| [< >] -> serror()

and parse_enum s =
	let doc = get_doc s in
	let meta = parse_meta s in
	match s with parser
	| [< name, p1 = any_enum_ident; params = parse_constraint_params; s >] ->
		let args = (match s with parser
		| [< '(POpen,_); l = psep Comma parse_enum_param; '(PClose,_) >] -> l
		| [< >] -> []
		) in
		let t = parse_type_opt s in
		let p2 = (match s with parser
			| [< p = semicolon >] -> p
			| [< >] -> serror()
		) in
		{
			ec_name = name;
			ec_doc = doc;
			ec_meta = meta;
			ec_args = args;
			ec_params = params;
			ec_type = t;
			ec_pos = punion p1 p2;
		}

and parse_enum_param = parser
	| [< '(Question,_); name, _ = ident ~allow_kwd:true; t = parse_type_hint >] -> (name,true,t)
	| [< name, _ = ident ~allow_kwd:true; t = parse_type_hint >] -> (name,false,t)

and push_flag_with_parser f = parser
	| [< >] -> push_flag f

and cc_block acc break s =
	if break then acc, break else
	try
		(* because of inner recursion, we can't put Display handling in errors below *)
		let e = try parse_cc_block_elt s with Display e -> display (EBlock (List.rev (e :: acc)),snd e) in
		cc_block (e :: acc) break s
	with
		| Stream.Failure -> (List.rev acc), break
		| BreakBlock -> (List.rev acc), true
		| Stream.Error _ ->
			let tk , pos = (match Stream.peek s with None -> last_token s | Some t -> t) in
			(!display_error) (Unexpected tk) pos;
			cc_block acc break s
		| Error (e,p) ->
			(!display_error) e p;
			cc_block acc break s

and parse_cc_block_elt = parser
	| [< e = expr; _ = semicolon >] -> e

and parse_cc_code s =
	if (!use_extended_syntax && (
			match !cc_arg_defs with
			| x::[] -> is_cc_scope x
			| _ -> false
		)) then begin
			let do_block s =
				push_flag discardPossibleClassFieldMemberFlag;
				let b,x = cc_block [] false s in
				let _ = pop_flag() in
				let e = match b with
					| [] -> EBlock b, null_pos
					| x::[] -> x
					| x::xs -> EBlock b, snd x
				in
				Some (e, x)
			in
			match s with parser
			| [< '(BrOpen, _); db=do_block; '(BrClose, _)>] -> db
			| [< >] -> do_block s
		end
	else None

and add_cl_sym_def_with_parser name pos is_ns fd = parser
		| [< >] -> add_cl_sym_def name pos ~new_scope:is_ns ~field_def:fd

and parse_var_or_const = parser
	| [< '(Kwd Var,p1) >] -> p1, false
	| [< '(Kwd KConst,p1) >] -> p1, true

and parse_opt_fun_args s =
	match Stream.peek s with
		| Some(Binop OpLt, _)  | Some(POpen, _) ->
			(match s with parser
			| [< pl = parse_constraint_params; '(POpen,_); al = psep Comma parse_fun_param; '(PClose,_) >] ->
				Some (pl, al))
		| _ -> None

and parse_class_field s =
	match !out_of_order_cfs with
	| x :: xs ->
		out_of_order_cfs := xs;
		x
	| [] ->
	let doc = get_doc s in
	let setla s = push_flag hasLocalAccessFlag in
	let clearla s = push_not_flag hasLocalAccessFlag in
	let check_init() =
		let ii = is_flag_set initInCCFlag in
		if ii then clear_flag initInCCFlag;
		ii
	in
	match s with parser
	| [< meta = parse_meta; al = parse_cf_rights true []; s >] ->
		let name, pos, k, meta, oal = (match s with parser
		| [< p1, is_const = parse_var_or_const; name, pn = dollar_ident ~allow_kwd:true; _ = add_cl_sym_def_with_parser name pn None (Some {ccfd_access=al;ccfd_mutable=not is_const;ccfd_meta=meta}); s >] ->
			(match s with parser
			| [< '(POpen,_); i1 = property_ident; '(Comma,_); i2 = property_ident; '(PClose,_) >] ->
				if is_const then serror() (*TODO better error msg*)
				else
					let t = parse_type_opt s in
					let e , p2 = (match s with parser
					| [< '(Binop OpAssign,_); _=setla; e = toplevel_expr; p2 = semicolon >] -> let _=pop_flag() in Some e , p2
					| [< '(Semicolon,p2) >] -> None , p2
					| [< >] -> serror()
				) in
				name, punion p1 p2, FProp (i1,i2,t, e), meta, None
			| [< t = parse_type_opt; s >] ->
				let e , p2, t = (match s with parser
				| [< '(Binop OpAssign,_); _=setla; e = toplevel_expr; p2 = semicolon >] ->
					let is_init = check_init() in
					let _ = pop_flag() in
					let is_init = check_init() || is_init in
					if is_init then begin
						(*print_string ("init_in_cc"^name^"\n");*)
						let ci, i = match !cc_arg_defs with
							| x::xs -> let i=List.length x.exprs in x,i
							| _ -> serror()
						in
						(*let fn = EFunction(Some("inline_if" ^ string_of_int i), {f_params=[];f_args=[];f_type=t;f_expr=Some e;}), p2 in*)
						ci.exprs <- (make_binop OpAssign (mk_ident name p1) e)::ci.exprs;
						let t = match t with
						| None -> Some(CTPath (mk_type_inf []))
						| _ -> t
						in
						None, p2, t
					end else 
						Some e , p2, t
				| [< '(Semicolon,p2) >] -> None , p2, t
				| [< >] -> serror()
				) in
				let k, meta, oal =
					if is_const then
						let oal =
							if not(List.mem APublic al || List.mem APrivate al) then
								Some APublic
							else None
						in
						let t =
							if t=None then Some(CTPath (mk_type_inf []))
							else t
						in FProp("default", "never", t, e), (Meta.AllowWrite , [mk_ident "new" p1], p1)::meta, oal
					else FVar(t, e), meta, None
				in
				name, punion p1 p2, k, meta, oal)
		| [< '(Kwd Def,p1); name = parse_fun_name; _ = add_cl_sym_def_with_parser name p1 (Some (SDFFunction name)) (Some {ccfd_access=al;ccfd_mutable=false;ccfd_meta=meta}); po = parse_opt_fun_args; t = parse_type_opt; s >] ->
			let pl, args, name, ooe = match po with
				| None ->
					let t = Some(CTPath (mk_type_inf [])) in
					let gname = "get_"^name in
					let ooe =
						if List.mem AOverride al then
							[]
						else
							let k = FProp("get", "never", t, None) in
							let cf = {cff_name = name; cff_doc = None; cff_meta = meta; cff_access = al; cff_pos = p1; cff_kind = k;} in
							out_of_order_cfs := !out_of_order_cfs @ [cf];
							let gto = mk_call "$getTypeOf" [mk_ident gname p1; mk_int "-1" p1] p1 in
							[mk_call "$setTypeOf" [mk_ident name p1; gto] p1]
					in
					[], [], "get_"^name, ooe
				| Some(pl, al) ->
					pl, al, name, []
			in
			let e, p2 =
				clearla s;
				let testsemi = match ooe with
				| [] -> true
				| _ -> false
				in
				let r =
					(match s with parser
					| [< '(Binop OpAssign, p); e = toplevel_expr; s >] ->
						if testsemi then (try ignore(semicolon s) with Error (Missing_semicolon,p) -> !display_error Missing_semicolon p);
						let e = EReturn (Some e), punion p (pos e) in
						Some e, pos e
					| [< e = toplevel_expr; s >] ->
						if testsemi then (try ignore(semicolon s) with Error (Missing_semicolon,p) -> !display_error Missing_semicolon p);
						Some e, pos e
					| [< '(Semicolon,p) >] -> None, p
					| [< >] -> serror()
					)
				in
				let _ = pop_flag() in
				r
			in
			let args, e = match e with
			| None -> args, e
			| Some e ->
				let args, e = adapt_fn_with_structure args e in
				args, Some e
			in
			let f = {
				f_params = pl;
				f_args = args;
				f_type = t;
				f_expr = e;
			} in
			out_of_order_exprs := !out_of_order_exprs @ ooe;
			name, punion p1 p2, FFun f, meta, None
		| [< '(Kwd Function,p1); name = parse_fun_name; _ = add_cl_sym_def_with_parser name p1 (Some (SDFFunction name)) (Some {ccfd_access=al;ccfd_mutable=false;ccfd_meta=meta}); pl = parse_constraint_params; '(POpen,_); al = psep Comma parse_fun_param; '(PClose,_); t = parse_type_opt; s >] ->
			let e, p2 =
				clearla s;
				let r =
					(match s with parser
					| [< e = toplevel_expr; s >] ->
						(try ignore(semicolon s) with Error (Missing_semicolon,p) -> !display_error Missing_semicolon p);
						Some e, pos e
					| [< '(Semicolon,p) >] -> None, p
					| [< >] -> serror()
					)
				in
				let _ = pop_flag() in
				r
			in
			let al, e = match e with
			| None -> al, e
			| Some e ->
				let al, e = adapt_fn_with_structure al e in
				al, Some e
			in
			let f = {
				f_params = pl;
				f_args = al;
				f_type = t;
				f_expr = e;
			} in
			name, punion p1 p2, FFun f, meta, None
		| [< _=setla; cc=parse_cc_code; s >] ->
			let _=pop_flag() in
			let hx() = if al = [] then raise Stream.Failure else serror() in
			match cc with
			| None -> hx()
			| Some(e, x) ->
				(*print_string ("parse_cc=>" ^ (s_expr e) ^"\n");
				print_string ((string_of_bool x) ^"\n");*)
				if x then raise (ContinueClassField (e, Semicolon))
				else
				(match Stream.peek s with
					(* | Some((At as t, _)) -> raise (ContinueClassField (e, t)) *)
					| Some((BrClose as t, _)) -> raise (ContinueClassField (e, t))
					| Some((Semicolon as t, _)) -> (*print_string(";\n");*) semicolon s;raise (ContinueClassField (e, t))
					| Some(t, _) -> (*print_string("fail or resume with " ^(s_token t)^"\n");*) hx()
					| _ -> hx())
		) in
		if is_flag_set initInCCFlag then clear_flag initInCCFlag;
		let al = match oal with
		| Some a -> a::al
		| _ -> al
		in
		{
			cff_name = name;
			cff_doc = doc;
			cff_meta = meta;
			cff_access = al;
			cff_pos = pos;
			cff_kind = k;
		}

and parse_cf_rights allow_static l = parser
	| [< '(Kwd Static,_) when allow_static; l = parse_cf_rights false (AStatic :: l) >] -> l
	| [< '(Kwd Macro,_) when not(List.mem AMacro l); l = parse_cf_rights allow_static (AMacro :: l) >] -> l
	| [< '(Kwd Public,_) when not(List.mem APublic l || List.mem APrivate l); l = parse_cf_rights allow_static (APublic :: l) >] -> l
	| [< '(Kwd Private,_) when not(List.mem APublic l || List.mem APrivate l); l = parse_cf_rights allow_static (APrivate :: l) >] -> l
	| [< '(Kwd Override,_) when not (List.mem AOverride l); l = parse_cf_rights false (AOverride :: l) >] -> l
	| [< '(Kwd Dynamic,_) when not (List.mem ADynamic l); l = parse_cf_rights allow_static (ADynamic :: l) >] -> l
	| [< '(Kwd Inline,_); l = parse_cf_rights allow_static (AInline :: l) >] -> l
	| [< >] -> l

and parse_fun_name = parser
	| [< name,_ = dollar_ident >] -> name
	| [< '(Kwd New,_) >] -> "new"

and parse_fun_param s =
	let hx s = match s with parser
		| [< '(Question,_); name, _ = dollar_ident_or_const; t = parse_type_opt; c = parse_fun_param_value >] -> (name,true,t,c)
		| [< name, _ = dollar_ident_or_const; t = parse_type_opt; c = parse_fun_param_value >] -> (name,false,t,c)
	in
	if !use_extended_syntax then begin
		match s with parser
		| [< '(BrOpen, p1); ds=parse_top_destructure_obj; '(BrClose, p2); t = parse_type_opt >] ->
			let name =  mk_fresh_name "__pst" in
			let rhs = mk_ident name p1 in
			let c = do_destructure_obj ~split_block:false ds (punion p1 p2) rhs in
			(name, false, t, Some c)
		| [< s >] -> hx s
	end else hx s

and parse_fun_param_value = parser
	| [< '(Binop OpAssign,_); e = toplevel_expr >] -> Some e
	| [< >] -> None

and parse_fun_param_type = parser
	| [< '(Question,_); name = ident; t = parse_type_hint >] -> (name,true,t)
	| [< name = ident; t = parse_type_hint >] -> (name,false,t)

and parse_constraint_params = parser
	| [< '(Binop OpLt,_); l = psep Comma parse_constraint_param; '(Binop OpGt,_) >] -> l
	| [< >] -> []

and parse_constraint_param = parser
	| [< name = type_name; s >] ->
		let params = (match s with parser
			| [< >] -> []
		) in
		let ctl = (match s with parser
			| [< '(DblDot,_); s >] ->
				(match s with parser
				| [< '(POpen,_); l = psep Comma parse_complex_type; '(PClose,_) >] -> l
				| [< t = parse_complex_type >] -> [t]
				| [< >] -> serror())
			| [< >] -> []
		) in
		{
			tp_name = name;
			tp_params = params;
			tp_constraints = ctl;
		}

and parse_class_herit ?(cc={cc_param=None;cc_super_args=null_pos, None;}) = parser
	| [< '(Kwd Extends,_); t = parse_type_path; s>] -> 
		if (!use_extended_syntax) then
			match s with parser
			| [< '(POpen,p1); s >] ->
				enter_scope cc_arg_defs (SDFFunction "extends");
				let e = 
					match s with parser
					| [<params = parse_call_params (mk_ident "super" p1); '(PClose,p2) >] ->
						cc.cc_super_args <- p1, Some(params);
						HExtends t
				in
					leave_scope cc_arg_defs;
					e
			| [< >] -> HExtends t
		else HExtends t
	| [< '(Kwd Implements,_); t = parse_type_path >] -> HImplements t

and block1 s =
	match Stream.npeek 2 s with
	| [(Kwd KConst, p); (DblDot, _)] ->
		Stream.junk s;
		block2 "const" (Ident "const") p s
	| [(Kwd Def, p); (DblDot, _)] ->
		Stream.junk s;
		block2 "def" (Ident "def") p s
	| _ ->
		(match s with parser
		| [< name,p = dollar_ident; s >] -> block2 name (Ident name) p s
		| [< '(Const (String name),p); s >] -> block2 (quote_ident name) (String name) p s
		| [< b = block [] >] -> EBlock b)

and block2 name ident p s =
	let default s =
		let e = expr_next (EConst ident,p) s in
		try
			let _ = semicolon s in
			let b = block [e] s in
			EBlock b
		with
			| Error (err,p) ->
				(!display_error) err p;
				EBlock (block [e] s)
	in
	match s with parser
	| [< '(DblDot,_); e = expr; l = parse_obj_decl >] -> EObjectDecl ((name,e) :: l)
	| [< s >] ->
		if !use_extended_syntax then
			match ident with
			| Ident _ ->
				(match Stream.peek s with
				| Some(Comma, _) ->
					let e = EConst ident,p in
					EObjectDecl ((name,e) :: (parse_obj_decl s))
				| _ -> default s)
			| _ -> default s
		else default s

and block acc s =
	try
		(* because of inner recursion, we can't put Display handling in errors below *)
		let racc = ref acc in
		(try 
				let e = parse_block_elt s in
				(match e with
				| (EBlock ((EConst(Ident sn), p)::xs), _) when p=null_pos && sn=struct_global_var_marker ->
					racc := xs @ !racc
				| _ ->
					racc := e :: !racc;
					());
		with
			| Display e -> display (EBlock (List.rev (e :: !racc)),snd e));
		block !racc s
	with
		| Stream.Failure ->
			List.rev acc
		| Stream.Error _ ->
			let tk , pos = (match Stream.peek s with None -> last_token s | Some t -> t) in
			(!display_error) (Unexpected tk) pos;
			block acc s
		| Error (e,p) ->
			(!display_error) e p;
			block acc s

and parse_block_elt s =
	let parse_var_or_const is_const p1 s =
		let hx s = 
			match s with parser
			| [< vl = parse_var_decls ~const:is_const p1; p2 = semicolon >] -> (EVars vl,punion p1 p2)
		in
		if !use_extended_syntax then begin
			match s with parser
			| [< '(BrOpen, p1); ds=parse_top_destructure_obj ; '(BrClose, p2); '(Binop OpAssign, _); rhs=expr; _ = semicolon >] ->
				do_destructure_obj ~const:is_const ds (punion p1 p2) rhs
			| [< s >] -> hx s
		end else hx s
	in
	match Stream.npeek 2 s with
	| [(Kwd KConst, p1); (BrOpen, _)] ->
		Stream.junk s;
		parse_var_or_const true p1 s
	| [(Kwd KConst, p1); (Const(Ident _), _)] ->
		Stream.junk s;
		parse_var_or_const true p1 s
	| [(Kwd KConst, p1); (Kwd _, _)] ->
		Stream.junk s;
		parse_var_or_const true p1 s
	| [(Kwd Var, p1); (BrOpen, _)] ->
		Stream.junk s;
		parse_var_or_const false p1 s
	| [(Kwd Var, p1); (Const(Ident _), _)] ->
		Stream.junk s;
		parse_var_or_const false p1 s
	| [(Kwd Var, p1); (Kwd _, _)] ->
		Stream.junk s;
		parse_var_or_const false p1 s
	| _ ->
		(match s with parser
		| [< '(Kwd Var,p1); s >] -> parse_var_or_const false p1 s
		| [< '(Kwd Inline,p1); '(Kwd Function,_); e = parse_function p1 true; _ = semicolon >] -> e
		| [< e = expr; _ = semicolon >] -> e)

and parse_obj_decl = parser
	| [< '(Comma,_); s >] ->
		if !use_extended_syntax then
			(match s with parser
			| [< name, p = ident_or_const; s >] ->
				(match Stream.peek s with
				| Some (Comma, _) -> (name, mk_ident name p) :: (parse_obj_decl s)
				| Some (BrClose, _) -> [name, mk_ident name p]
				| _ ->
					(match s with parser
					| [< '(DblDot,_); e = expr; l = parse_obj_decl >] -> (name,e) :: l
					| [< >] -> []))
			| [< '(Const (String name),_); '(DblDot,_); e = expr; l = parse_obj_decl >] -> (quote_ident name,e) :: l
			| [< >] -> [])
		else
			(match s with parser
			| [< name, _ = ident_or_const; '(DblDot,_); e = expr; l = parse_obj_decl >] -> (name,e) :: l
			| [< '(Const (String name),_); '(DblDot,_); e = expr; l = parse_obj_decl >] -> (quote_ident name,e) :: l
			| [< >] -> [])
	| [< >] -> []

and parse_array_decl = parser
	| [< e = expr; s >] ->
		(match s with parser
		| [< '(Comma,_); l = parse_array_decl >] -> e :: l
		| [< >] -> [e])
	| [< >] ->
		[]

and parse_tuple acc = parser
	| [< e = expr; s >] ->
		(match s with parser
		| [< '(Comma,_); l = parse_tuple (e::acc) >] -> l
		| [< >] -> e::acc)
	| [< >] -> acc

and parse_var_decl_head ?(const=false) = parser
	| [< meta = parse_meta; name, p = dollar_ident ~allow_kwd:true; t = parse_type_opt >] ->
		let meta = if const then (Meta.Const,[],p)::meta else meta in
		(name,t,meta)

and parse_var_assignment = parser
	| [< '(Binop OpAssign,p1); s >] ->
		begin match s with parser
		| [< e = expr >] -> Some e
		| [< >] -> error (Custom "expression expected after =") p1
		end
	| [< >] -> None

and parse_var_decls_next ?(const=false) vl = parser
	| [< '(Comma,p1); name,t,meta = parse_var_decl_head ~const:const; s >] ->
		begin try
			let eo = parse_var_assignment s in
			parse_var_decls_next ~const:const ((name,t,eo,meta) :: vl) s
		with Display e ->
			let v = (name,t,Some e, meta) in
			let e = (EVars(List.rev (v :: vl)),punion p1 (pos e)) in
			display e
		end
	| [< >] -> vl

and parse_tuple_head ?(const=false) index s =
	let name, t, meta = parse_var_decl_head s in
	let meta = if const then (Meta.Const,[],null_pos)::meta else meta in
	name, t, index, meta

and parse_tuple_assigment_next ?(const=false) vl index = parser
	| [< '(Comma,p1); s; >] ->
		(match Stream.peek s with
		| Some(t, _)  when t=PClose -> vl
		| _ -> 
			(match s with parser 
			| [< name,t, i, meta = parse_tuple_head ~const:const index; s >] ->
				begin try
					let vl = if name="_" then vl else (name, t, i, meta)::vl in
					parse_tuple_assigment_next vl (i+1) s
				with Display e ->
					let v = name,t,None, meta in
					let vl = List.map (fun (n,t,i,m) -> n,t,None,m) vl in
					let e = (EVars(List.rev (v :: vl)),punion p1 (pos e)) in
					display e
				end
			| [< >] -> vl))
	| [< >] -> vl

and parse_tuple_assignment ?(const=false) index = parser
	[< name, t, i, meta = parse_tuple_head ~const:const index; s >] ->
		let acc = if name="_" then [] else [name, t, i, meta] in
		parse_tuple_assigment_next ~const:const acc (i+1) s

and parse_var_decls ?(const=false) p1 = parser
	| [< '(POpen, p1); l=parse_tuple_assignment ~const:const 1; '(PClose, p2); s >] ->
		(match parse_var_assignment s with
		| Some(e) ->
			List.map (fun (n,t,i,m) ->
				let ef = EField (e, ("_" ^ (string_of_int i))) in
				let e = Some (ef, pos e) in
				n,t,e,m
			) l
		| _ -> error (Custom "Assignment required for tuple") p1)
	| [< name,t, meta = parse_var_decl_head ~const:const; s >] ->
		let eo = parse_var_assignment s in
		List.rev (parse_var_decls_next ~const:const [name,t,eo,meta] s)
	| [< s >] -> error (Custom "Missing variable identifier") p1

and parse_var_decl ?(const=false) = parser
	| [< name,t,meta = parse_var_decl_head ~const:const; eo = parse_var_assignment >] -> (name,t,eo,meta)

and inline_function = parser
	| [< '(Kwd Inline,_); '(Kwd Function,p1) >] -> true, p1
	| [< '(Kwd Function,p1) >] -> false, p1

and reify_expr e =
	let to_expr,_,_ = reify !in_macro in
	let e = to_expr e in
	(ECheckType (e,(CTPath { tpackage = ["haxe";"macro"]; tname = "Expr"; tsub = None; tparams = [] })),pos e)

and parse_macro_expr p = parser
	| [< '(DblDot,_); t = parse_complex_type >] ->
		let _, to_type, _  = reify !in_macro in
		let t = to_type t p in
		(ECheckType (t,(CTPath { tpackage = ["haxe";"macro"]; tname = "Expr"; tsub = Some "ComplexType"; tparams = [] })),p)
	| [< '(Kwd Var,p1); vl = psep Comma parse_var_decl >] ->
		reify_expr (EVars vl,p1)
	| [< d = parse_class None [] [] false >] ->
		let _,_,to_type = reify !in_macro in
		(ECheckType (to_type d,(CTPath { tpackage = ["haxe";"macro"]; tname = "Expr"; tsub = Some "TypeDefinition"; tparams = [] })),p)
	| [< e = secure_expr >] ->
		reify_expr e

and parse_function p1 inl = parser
	| [< name = popt dollar_ident; pl = parse_constraint_params; '(POpen,_); al = psep Comma parse_fun_param; '(PClose,_); t = parse_type_opt; s >] ->
		let make e =
			let al, e = adapt_fn_with_structure al e in
			let f = {
				f_params = pl;
				f_type = t;
				f_args = al;
				f_expr = Some e;
			} in
			EFunction ((match name with None -> None | Some (name,_) -> Some (if inl then "inline_" ^ name else name)),f), punion p1 (pos e)
		in
		(try
			expr_next (make (secure_expr s)) s
		with
			Display e -> display (make e))

and parse_for_init s =
	if !use_extended_syntax then
		match s with parser
		| [< '(Kwd Var,p1); vl = parse_var_decls p1; p2 = semicolon >] -> (EVars vl,punion p1 p2), false
		| [< '(Kwd Inline,p1); '(Kwd Function,_); e = parse_function p1 true; _ = semicolon >] -> e, false
		| [< e = expr; s >] ->
			let efor =
				match Stream.peek s with
				| Some((t,_)) when t=Semicolon ->
					Stream.junk s;
					false
				| _ -> true
			in e, efor
	else (expr s), true

and parse_top_destructure_obj s =
	parse_destructure_obj (mk_structure_elm ("","")) s

and parse_destructure_obj ds s =
	let pdds = parse_destructure_obj_decl ds in
	let _ = psep Comma pdds s in
	ds.globals <- List.rev ds.globals;
	ds.globals_def <- List.rev ds.globals_def;
	ds.structures <- List.rev ds.structures;
	ds

and parse_destructure_obj_def = parser
	| [< '(Binop OpAssign, p); e2=expr >] -> Some e2
	| [< >] -> None

and parse_destructure_obj_decl ds s =
	match s with parser
	| [< name,p = dollar_ident; s >] ->
		let np = name,p in
			(match s with parser
			| [< '(DblDot, _); s >] ->
				(match s with parser
				| [< '(BrOpen,p3); s >] ->
					let fn = mk_fresh_name struct_var_name_prefix ~sfx:("_"^name) in
					let nds =
						let tmp = mk_structure_elm (fn, name) in
						ds.structures <- tmp::ds.structures;
						tmp
					in
					(match s with parser
					| [< _=parse_destructure_obj nds; '(BrClose, p) >] ->
						ds.protected <-  (nds.protected || ds.protected)
					| [< >] -> serror())
				| [< name2,p2=dollar_ident; def=parse_destructure_obj_def >] ->
					(match def with
					| Some e ->
						ds.protected <- true; 
						ds.globals_def <- ((name2,p2), np, e)::ds.globals_def
					| _ -> ds.globals <- ((name2,p2), np)::ds.globals))
			| [< s >] ->
				(match parse_destructure_obj_def s with
				| Some e ->
					ds.protected <- true; 
					ds.globals_def <- (np, np, e)::ds.globals_def
				| _ -> ds.globals <- (np, np)::ds.globals)
			)

and do_destructure_obj ?(split_block=true) ?(const=false) ds p1 e2 =
	let to_null p = ECast((mk_ident "null" p),None),p in
	(*let untyped e = EUntyped e, (pos e) in*)
	let untyped e = e in
	let p2 = pos e2 in
	let rec for_all_ds ?(parent=None) fn acc wl =
		match wl with
		| [] -> acc
		| ds::xs ->
			let acc = fn acc parent ds in
			for_all_ds ~parent:(Some ds) fn acc (ds.structures@xs)
	in
	let mk_assign var base field = make_binop OpAssign var (EField (base, field) , pos base) in
	let if_not_null o e1 e2 =
		let p = pos o in
		let test = (make_binop OpNotEq o (to_null p)) in
		EIf (test, e1, e2), p
	in
	let if_null_assign o e1 =
		let p = pos o in
		let test = (make_binop OpEq o (to_null p)) in
		let assign = make_binop OpAssign o e1 in
		EIf (test, assign, None), p
	in
	let e_null = Some (to_null p2) in
	let mk_vars (gacc, sacc) parent ds =
		let gacc = List.fold_left  (fun acc ((n,p),_) -> (n, None, e_null, [])::acc) gacc ds.globals in
		let gacc = List.fold_left  (fun acc ((n,p),_,_) -> (n, None, e_null, [])::acc) gacc ds.globals_def in
		let vn,fn = ds.name in
		let sacc = if (fn="") then sacc else ((vn, None, e_null, [])::sacc) in
		(gacc, sacc)
	in
	let gvars, svars = for_all_ds mk_vars ([], []) [ds] in
	let b2 = [(EVars (List.rev svars), p1) ] in
	let gvars = match e2 with
		| EConst (Ident n), _ ->
			ds.name <- (n, "");
			gvars
		| _ -> 
			let n = mk_fresh_name struct_var_name_prefix in
			ds.name <- (n, "");
			(n, None, (Some e2), [])::gvars
	in
	let gvars = List.rev gvars in
	let cvars =
		if const then
			List.map (fun (n, _, eo, _) -> 
				let p = match eo with
					| Some(e) -> pos e
					| _ -> p2
				in
				EField ((mk_ident n p), "__to_const__"), p
			) gvars
		else []
	in
	let gvars = (EVars (gvars), p1) in
	let rec loop pn acc wl =
		match wl with
		| [] -> acc
		| ds::xs ->
			let vn,on = ds.name in
			let obj_name = EConst(Ident vn) in
			let eobj_name = obj_name, p2 in
			let init_global acc g =
				match g with
				| (vn, vp), (fn, fp) ->
					let var = (mk_ident vn vp) in
					let base = (obj_name, fp) in
					let assign = mk_assign var base fn in
					let assign = untyped assign in
					assign::acc
			in
			let init_global_def acc gd =
				match gd with
				| (vn, vp), (fn, fp), _ ->
					let var = (mk_ident vn vp) in
					let base = (obj_name, fp) in
					let assign = mk_assign var base fn in
					let assign = untyped assign in
					assign::acc
			in
			let init_struct_assign acc ds =
				let vn,on = ds.name in
				(mk_assign (mk_ident vn p2) eobj_name on)::acc
			in
			let assign_first acc =
				match pn with
				| None -> acc
				| Some e ->
					let assign = mk_assign eobj_name e on in
					let assign = untyped assign in
					assign::acc
			in
			let acc = assign_first acc in
			let acc, eobj_name =
				if ds.protected then
					let bt = 
						let acc=List.fold_left init_global_def [] ds.globals_def in
						let acc=List.fold_left init_struct_assign acc ds.structures in
						acc
					in
					let t = EBlock bt, p2 in
					((if_not_null eobj_name t None)::acc), None
				else
					acc, Some eobj_name
			in
			let acc = List.fold_left init_global acc ds.globals in
			loop eobj_name acc (ds.structures@xs)
	in 
	let b2 = loop None b2 [ds] in
	let b2 = for_all_ds (fun acc p ds -> List.fold_left (fun acc ((n,p),_,e) -> (if_null_assign (mk_ident n p) e)::acc) acc ds.globals_def) b2 [ds] in
	let b2 = List.rev b2 in
	let b2 =
		if split_block then [(EBlock b2), p2;gvars]
		else gvars::b2
	in
	EBlock ((mk_ident struct_global_var_marker null_pos)::(cvars@b2)), p2

and adapt_fn_with_structure fn_params fn_body =
	if !use_extended_syntax then
		let p = pos fn_body in
		let b = ref [] in
		let apply (n,t,o,v)  =
			match v with
			| None -> (n,t,o,v)
			| Some (EBlock ((EConst(Ident sn), p)::xs), _) when p=null_pos && sn=struct_global_var_marker ->
				b := xs @ !b;
				(n,t,o,None)
			| _ -> (n,t,o,v)
		in
		let fn_params = List.map apply (fn_params) in
		if (List.length !b)=0 then fn_params, fn_body
		else
			let b2 = match fn_body with
				| EBlock b2, _ -> !b @ b2
				| _ -> !b
			in fn_params, (EBlock b2, p)
	else fn_params, fn_body

and expr_with_flag f s =
 	push_flag f;
 	expr s

and expr_with_not_flag f s =
 	push_not_flag f;
 	expr s

and last_parsed_token s = (match Stream.peek s with None -> last_token s | Some t -> t)

and parse_cc_param_with_ac meta ac (mode, im) s =
	match s with parser
	| [< '(Question,_); name, pn = dollar_ident; t = parse_type_opt; c = parse_fun_param_value; s>] ->
			let tok,pos = last_parsed_token s in 
			{arg=(ac, punion pn pos, (name, true, t, c));mode=mode;is_mutable=im;use_cnt=0;meta=meta;}
	| [< name, pn = dollar_ident; t = parse_type_opt; c = parse_fun_param_value; s>] ->
			let tok,pos = last_parsed_token s in
			{arg=(ac, punion pn pos, (name, false, t , c));mode=mode;is_mutable=im;use_cnt=0;meta=meta;}

and parse_mandatory_type n p = parser
	| [< t = parse_type_hint >] -> Some t
	| [< >] -> error (Custom ("Explicit type required for field " ^ n)) p (* until i know how to resolve delayed type *)

and parse_cc_param = parser
	| [< meta = parse_meta; ac = parse_cc_param_opt_access; m = parse_cc_param_opt_modifier; s >] -> parse_cc_param_with_ac meta ac m s

and parse_class_constructor n s =
	enter_scope cl_sym_defs (SDFClass n);
	let no_arg = {cc_param=None; cc_super_args=null_pos, None;} in
	if !use_extended_syntax then
		match s with parser
			| [< ac = parse_cc_opt_access; cp = parse_constraint_params; s >] ->
				(match s with parser
				| [< '(POpen,o1); s >] ->
					push_flag ccDefinedFlag; 
					(match s with parser 
					| [< al = psep Comma parse_cc_param;'(PClose,o2) >] ->
						enter_scope cc_arg_defs (SDFClass n);
						let scope = List.hd !cc_arg_defs in 
						List.iter(fun arg -> match arg with {arg=(_, _ , (n1, _, _, _)); _} -> Hashtbl.add scope.ht n1 arg) al;
						{
							cc_param = Some 
							{
								cc_access = ac;
								cc_params = cp;
								cc_args = al;
								cc_open_par = o1;
								cc_close_par = o2;
							};
							cc_super_args = null_pos, None;
						}
					| [< >] -> no_arg)
				| [< >] -> no_arg)
			| [< >] -> no_arg
	else no_arg

and use_def_expr e =
	if !use_extended_syntax && (is_flag_set ccDefinedFlag) then begin
		let hla = is_flag_set hasLocalAccessFlag in
		match e with
		| EConst(Ident n), _ ->
			(*print_string((s_expr e) ^ " : " ^ (string_of_bool hla)^"\n");*)
			use_def hla n;
			e
		| EField ((EConst (Ident "this"), _), n), _ ->
			(*print_string((s_expr e) ^ " : " ^ (string_of_bool hla)^"\n");*)
			use_def ~check_scope:false false n;
			e
		| _ -> e
	end else e

and expr s =
	match !out_of_order_exprs with
	| x::xs ->
		out_of_order_exprs := xs;
		x
	| [] ->
	if !use_extended_syntax && (is_flag_set discardPossibleClassFieldMemberFlag) then
		(match Stream.peek s with
		| Some (t, _) ->
			(*print_string ((s_token t) ^"\n");*)
			(match t with
			 | At | Kwd Var | Kwd KConst | Kwd Public | Kwd Override | Kwd Private | Kwd Inline | Kwd Static | Kwd Function | Kwd Def -> raise BreakBlock
			 | _ -> ())
		| None -> ());

	let hx s = match s with parser
	| [< (name,params,p) = parse_meta_entry; s >] ->
		(try
			make_meta name params (secure_expr s) p
		with Display e ->
			display (make_meta name params e p))
	| [< '(BrOpen,p1); b = block1; '(BrClose,p2); s >] ->
		let e = (b,punion p1 p2) in
		(match b with
		| EObjectDecl _ -> expr_next e s
		| _ -> e)
	| [< '(Kwd Macro,p); s >] -> parse_macro_expr p s
	| [< '(Kwd Var,p1); v = parse_var_decl >] -> EVars [v], p1
	| [< '(Const c,p); s >] -> expr_next (use_def_expr (EConst c,p)) s
	| [< '(Kwd This,p); s >] -> use_def_expr (expr_next (mk_this p) s)
	| [< '(Kwd True,p); s >] -> expr_next (EConst (Ident "true"),p) s
	| [< '(Kwd False,p); s >] -> expr_next (EConst (Ident "false"),p) s
	| [< '(Kwd Null,p); s >] -> expr_next (EConst (Ident "null"),p) s
	| [< '(Kwd Cast,p1); s >] ->
		(match s with parser
		| [< '(POpen,pp); e = expr; s >] ->
			(match s with parser
			| [< '(Comma,_); t = parse_complex_type; '(PClose,p2); s >] -> expr_next (ECast (e,Some t),punion p1 p2) s
			| [< t = parse_type_hint; '(PClose,p2); s >] ->
				let ep = EParenthesis (ECheckType(e,t),punion p1 p2), punion p1 p2 in
				expr_next (ECast (ep,None),punion p1 (pos ep)) s
			| [< '(PClose,p2); s >] ->
				let ep = expr_next (EParenthesis(e),punion pp p2) s in
				expr_next (ECast (ep,None),punion p1 (pos ep)) s
			| [< >] -> serror())
		| [< e = secure_expr >] -> expr_next (ECast (e,None),punion p1 (pos e)) s)
	| [< '(Kwd Throw,p); e = expr >] -> (EThrow e,p)
	| [< '(Kwd New,p1); t = parse_type_path; '(POpen,p); s >] ->
		if is_resuming p then display (EDisplayNew t,punion p1 p);
		(match s with parser
		| [< al = psep Comma expr; '(PClose,p2); s >] -> expr_next (ENew (t,al),punion p1 p2) s
		| [< >] -> serror())
	| [< '(POpen,p1); s >] ->
		let hx s = 
			match s with parser
			| [< e=(expr_with_not_flag noDbldotFlag); s >] ->
			 (match s with parser
				| [< '(PClose,p2); s >] ->
					let e = (EParenthesis e, punion p1 p2) in
					let pot = is_flag_set parseOptTypeFlag in
					let _ = pop_flag() in
					let e = 
						if pot then
							let _=pop_flag() in
							let t = parse_type_opt s in
							ECast (e,t), p2
						else e
					in
					expr_next e s
				| [< t = parse_type_hint; '(PClose,p2); s >] -> 
					let _=pop_flag() in
					expr_next (EParenthesis (ECheckType(e,t),punion p1 p2), punion p1 p2) s
				| [< '(Comma, _); es=parse_tuple [e]; s >] -> 
					(match s with parser
					| [<' (PClose,p2); s>] ->
						let cnt = List.length es in
						let t = mk_type [] "Tuple" [] (Some("Tuple"^(string_of_int cnt))) in
						expr_next (ENew (t, List.rev es), punion p1 p2) s
					| [< >] -> serror())
				| [< >] -> serror())
		in
		if !use_extended_syntax then
			match Stream.npeek 2 s with
			| [(PClose, p2); (Binop OpArrow, _)] ->
				Stream.junk s;
				let p = punion p1 p2 in
				expr_next (EConst (Ident ""), p) s
			| _ -> hx s
		else
			hx s
	| [< '(BkOpen,p1); l = parse_array_decl; '(BkClose,p2); s >] -> expr_next (EArrayDecl l, punion p1 p2) s
	| [< '(Kwd Function,p1); e = parse_function p1 false; >] -> e
	| [< '(Unop op,p1) when is_prefix op; e = expr >] -> make_unop op e p1
	| [< '(Binop OpSub,p1); e = expr >] ->
		let neg s =
			if s.[0] = '-' then String.sub s 1 (String.length s - 1) else "-" ^ s
		in
		(match make_unop Neg e p1 with
		| EUnop (Neg,Prefix,(EConst (Int i),pc)),p -> EConst (Int (neg i)),p
		| EUnop (Neg,Prefix,(EConst (Float j),pc)),p -> EConst (Float (neg j)),p
		| e -> e)
	(*/* removed unary + : this cause too much syntax errors go unnoticed, such as "a + + 1" (missing 'b')
						without adding anything to the language
	| [< '(Binop OpAdd,p1); s >] ->
		(match s with parser
		| [< '(Const (Int i),p); e = expr_next (EConst (Int i),p) >] -> e
		| [< '(Const (Float f),p); e = expr_next (EConst (Float f),p) >] -> e
		| [< >] -> serror()) */*)
	| [< '(Kwd For,p); '(POpen,po); it,hx=parse_for_init; s >] ->
		let efor s =
			push_for_ctx None;
			try
				let e = secure_expr s in
				pop_for_ctx();
				(EFor (it,e),punion p (pos e))
			with 
				Display e ->
					pop_for_ctx();
					display (EFor (it,e),punion p (pos e))
		in
		if hx then
			match s with parser [< '(PClose,_); s >] -> efor s
		else
			(match s with parser 
			| [< cond=expr; '(Semicolon,_); stop=expr; '(PClose,_); s >] ->
				push_for_ctx (Some stop);
				(try
					let e = secure_expr s in
					let pe = pos e in
					let e = EBlock (e::stop::[]), punion (pos stop) pe in
					let w = EWhile (cond,e,NormalWhile),punion p pe in
					pop_for_ctx();
					EBlock (it::w::[]), pos w
				with
					Display e ->
						let w =
							let pe = pos e in
							let e = EBlock (e::stop::[]), punion (pos stop) pe in
							EWhile (cond,e,NormalWhile),punion p pe
						in
							pop_for_ctx();
							display (EBlock (it::w::[]), pos w)))
	| [< '(Kwd If,p); '(POpen,_); cond = expr; '(PClose,_); e1 = expr; s >] ->
		let e2 = (match s with parser
			| [< '(Kwd Else,_); e2 = expr; s >] -> Some e2
			| [< >] ->
				match Stream.npeek 2 s with
				| [(Semicolon,_); (Kwd Else,_)] ->
					Stream.junk s;
					Stream.junk s;
					Some (secure_expr s)
				| _ ->
					None
		) in
		(EIf (cond,e1,e2), punion p (match e2 with None -> pos e1 | Some e -> pos e))
	| [< '(Kwd Return,p); e = popt expr >] -> (EReturn e, match e with None -> p | Some e -> punion p (pos e))
	| [< '(Kwd Break,p) >] -> (EBreak,p)
	| [< '(Kwd Continue,p) >] ->
		let c = EContinue, p in
		(match peek_for_ctx() with
		| None -> c
		| Some(e) -> (EBlock (e::c::[])), p)
	| [< '(Kwd While,p1); '(POpen,_); cond = expr; '(PClose,_); s >] ->
		for_ctx := None :: !for_ctx;
		(try
			let e = secure_expr s in
			pop_for_ctx();
			(EWhile (cond,e,NormalWhile),punion p1 (pos e))
		with
			Display e ->
				pop_for_ctx();
				display (EWhile (cond,e,NormalWhile),punion p1 (pos e)))
	| [< '(Kwd Do,p1); e = expr; '(Kwd While,_); '(POpen,_); cond = expr; '(PClose,_); >] ->
		pop_for_ctx();
		(EWhile (cond,e,DoWhile),punion p1 (pos e))
	| [< '(Kwd Switch,p1); e = expr; '(BrOpen,_); cases , def = parse_switch_cases e []; '(BrClose,p2); s >] -> (ESwitch (e,cases,def),punion p1 p2)
	| [< '(Kwd Try,p1); e = expr; cl = plist (parse_catch e); >] -> (ETry (e,cl),p1)
	| [< '(IntInterval i,p1); e2 = expr >] -> make_binop OpInterval (EConst (Int i),p1) e2
	| [< '(Kwd Untyped,p1); e = expr; s>] -> (EUntyped e,punion p1 (pos e))
	| [< '(Dollar v,p); s >] -> expr_next (EConst (Ident ("$"^v)),p) s
	in
	match Stream.npeek 2 s with
	| [(Kwd KConst, p); (t, _)] ->
		(match t with
		| Const (Ident _) ->
			hx s
		| _ ->
			Stream.junk s;
			use_def_expr (expr_next (mk_ident "const" p) s))
	| [(Kwd Def, p); (t, _)] ->
		(match t with
		| Const (Ident _) ->
			hx s
		| _ ->
			Stream.junk s;
			use_def_expr (expr_next (mk_ident "def" p) s))
	| _ -> hx s

and sl_id = ("$@sl",None,None,[])

and expr_next e1 = parser
	| [< '(BrOpen,p1) when is_dollar_ident e1; eparam = expr; '(BrClose,p2); s >] ->
		(match fst e1 with
		| EConst(Ident n) -> expr_next (EMeta((Common.MetaInfo.from_string n,[],snd e1),eparam), punion p1 p2) s
		| _ -> assert false)
	| [< '(Dot,p); s >] ->
		if is_resuming p then display (EDisplay (e1,false),p);
		(match s with parser
		| [< '(Kwd Macro,p2) when p.pmax = p2.pmin; s >] -> expr_next (EField (e1,"macro") , punion (pos e1) p2) s
		| [< '(Kwd New,p2) when p.pmax = p2.pmin; s >] -> expr_next (EField (e1,"new") , punion (pos e1) p2) s
		| [< '(Kwd KConst,p2) when p.pmax = p2.pmin; s >] -> expr_next (EField (e1,"const") , punion (pos e1) p2) s
		| [< '(Kwd Def,p2) when p.pmax = p2.pmin; s >] -> expr_next (EField (e1,"def") , punion (pos e1) p2) s
		| [< '(Const (Ident f),p2) when p.pmax = p2.pmin; s >] -> expr_next (EField (e1,f) , punion (pos e1) p2) s
		| [< '(Dollar v,p2); s >] -> expr_next (EField (e1,"$"^v) , punion (pos e1) p2) s
		| [< '(Binop OpOr,p2) when do_resume() >] ->
			set_resume p;
			display (EDisplay (e1,false),p) (* help for debug display mode *)
		| [< >] ->
			(* turn an integer followed by a dot into a float *)
			match e1 with
			| (EConst (Int v),p2) when p2.pmax = p.pmin -> expr_next (EConst (Float (v ^ ".")),punion p p2) s
			| _ -> serror())
	| [< '(POpen,p1); s >] ->
		if is_resuming p1 then display (EDisplay (e1,true),p1);
		(match s with parser
		| [< '(Binop OpOr,p2) when do_resume() >] ->
			set_resume p1;
			display (EDisplay (e1,true),p1) (* help for debug display mode *)
		| [< params = parse_call_params e1; '(PClose,p2); s >] -> expr_next (ECall (e1,params) , punion (pos e1) p2) s
		| [< >] -> serror())
	| [< '(BkOpen,_); e2 = expr; '(BkClose,p2); s >] ->
		expr_next (EArray (e1,e2), punion (pos e1) p2) s
	| [< '(Binop OpGt,p1); s >] ->
		(match s with parser
		| [< '(Binop OpGt,p2) when p1.pmax = p2.pmin; s >] ->
			(match s with parser
			| [< '(Binop OpGt,p3) when p2.pmax = p3.pmin >] ->
				(match s with parser
				| [< '(Binop OpAssign,p4) when p3.pmax = p4.pmin; e2 = expr >] -> make_binop (OpAssignOp OpUShr) e1 e2
				| [< e2 = secure_expr >] -> make_binop OpUShr e1 e2)
			| [< '(Binop OpAssign,p3) when p2.pmax = p3.pmin; e2 = expr >] -> make_binop (OpAssignOp OpShr) e1 e2
			| [< e2 = secure_expr >] -> make_binop OpShr e1 e2)
		| [< '(Binop OpAssign,p2) when p1.pmax = p2.pmin; s >] ->
			make_binop OpGte e1 (secure_expr s)
		| [< e2 = secure_expr >] ->
			make_binop OpGt e1 e2)
	| [< '(Binop op,_); s >] ->
		let mk_binop e2 =
			let e = make_binop op e1 e2 in
			if !use_extended_syntax then
				match  op with
				| OpArrow ->
					let e1, t = match e1 with
						| ECast (e, t), _ -> e, t
						| _ -> e1, None
					in
					let mk_fn args e = 
						let e =
							match e with
							| EBlock _, _ -> e
							| _ -> (EReturn (Some e)), pos e
						in
						let f = {
							f_params = [];
							f_type = t;
							f_args = args;
							f_expr = Some e;
							} 
						in
						EFunction (None,f), pos e
					in
					let mk_fn_from_l l e =
						let l = List.filter(fun (n,o,t,m) -> (n<>"") && (n<>"$@sl")) l in
						let l = List.map(fun (n,o,t,m) -> let b,n = opt_ident n in n,b,o,t) l in
						mk_fn (List.rev l) e2
					in
					(match e1 with
					| EConst(Ident id),p ->
						 	if id="" then mk_fn [] e2
						 	else
							 	let o, id = opt_ident id in
							 	if is_lower_ident id then mk_fn [(id,o,None,None)] e2
							 	else e
					| EParenthesis (EVars l, _), _ | EVars l,_ -> mk_fn_from_l l e2
					| _ -> mk_fn [] e2) 
				| _ -> e
			else e
		in
		(try
			(match s with parser
			| [< e2 = expr >] -> mk_binop e2
			| [< >] -> serror())
		with Display e2 ->
			display (mk_binop e2))
	| [< '(Unop op,p) when is_postfix e1 op; s >] ->
		expr_next (EUnop (op,Postfix,e1), punion (pos e1) p) s
	| [< '(Question,_); e2 = (expr_with_flag noDbldotFlag); '(DblDot,_); e3 = expr >] ->
		let _ = pop_flag() in
		(ETernary (e1,e2,e3),punion (pos e1) (pos e3))
	| [< '(Kwd In,_); e2 = expr >] ->
		(EIn (e1,e2), punion (pos e1) (pos e2))
	| [< s >] ->
		let tok = Stream.peek s in
		if !use_extended_syntax && not (is_flag_set noDbldotFlag) then
			let pis = ref !Lexer.prev_is_space in
			match tok with
			| Some((Semicolon ,_)) | Some((Comma, _))| Some((BkClose, _)) -> e1
			| Some((tok, _)) ->
				let e1_args =
					match e1 with
					| EConst(Ident n1), p ->
						let o,n = opt_ident n1 in
						if is_lower_ident n then
							let t1 = 
								if tok=DblDot then
									let t = parse_type_opt s in
									pis := !Lexer.prev_is_space;
									t
								else None
							in
							Some(sl_id::(n1,t1,None,[])::[], p)
						else None
					| EVars (x::xs), p when x=sl_id -> Some(x::xs, p)
					| _ -> None
				in
				(match e1_args with
				| Some((x::l, p)) ->
					(match Stream.npeek 2 s with
						| [(PClose, _); (Binop OpArrow, _)] -> EVars(x::l), p
						| [(Binop OpArrow, _); _] -> expr_next (EVars(x::l),p) s
						| [(PClose, p2); (tok, p)] ->
							if tok=DblDot then begin
								push_flag parseOptTypeFlag;
								EVars(x::l), p
							end else
								(match l with
								| (n, Some(t), None, [])::[] when x=sl_id -> ECheckType(e1,t),punion p p2
								| _ -> e1)
						| [(tok, _); _] when !pis ->
							(match s with parser
							| [< '(Const (Ident n2),p2) ; s >] ->
								let o,n = opt_ident n2 in
								if is_lower_ident n then
									let t2 =
										match Stream.peek s with
										| Some((DblDot, _)) -> parse_type_opt s
										| _ -> None
									in expr_next (EVars(sl_id::(n2,t2,None,[])::l), punion p p2) s
								else e1
							| [< >] -> e1)
						| _ -> e1
					)
				| _ -> e1)
			| _ -> e1
		else e1

and parse_guard = parser
	| [< '(Kwd If,p1); '(POpen,_); e = expr; '(PClose,_); >] -> e

and parse_switch_cases eswitch cases =
	let noDbldot s = push_flag noDbldotFlag in
	parser
	| [< '(Kwd Default,p1); '(DblDot,_); s >] ->
		let b = (try block [] s with Display e -> display (ESwitch (eswitch,cases,Some (Some e)),punion (pos eswitch) (pos e))) in
		let b = match b with
			| [] -> None
			| _ -> Some ((EBlock b,p1))
		in
		let l , def = parse_switch_cases eswitch cases s in
		(match def with None -> () | Some _ -> error Duplicate_default p1);
		l , Some b
	| [< '(Kwd Case,p1); _=noDbldot; el = psep Comma expr; eg = popt parse_guard; '(DblDot,_); s >] ->
		let _=pop_flag() in
		(match el with
		| [] -> error (Custom "case without a pattern is not allowed") p1
		| _ ->
			let b = (try block [] s with Display e -> display (ESwitch (eswitch,List.rev ((el,eg,Some e) :: cases),None),punion (pos eswitch) (pos e))) in
			let b = match b with
				| [] -> None
				| _ -> Some ((EBlock b,p1))
			in
			parse_switch_cases eswitch ((el,eg,b) :: cases) s
		)
	| [< >] ->
		List.rev cases , None

and parse_catch etry = parser
	| [< '(Kwd Catch,p); '(POpen,_); name, _ = dollar_ident; s >] ->
		match s with parser
		| [< t = parse_type_hint; '(PClose,_); s >] ->
			(try
				(name,t,secure_expr s)
			with
				Display e -> display (ETry (etry,[name,t,e]),punion (pos etry) (pos e)))
		| [< '(_,p) >] -> error Missing_type p

and parse_call_params ec s =
	let e = (try
		match s with parser
		| [< e = expr >] -> Some e
		| [< >] -> None
	with Display e ->
		display (ECall (ec,[e]),punion (pos ec) (pos e))
	) in
	let rec loop acc =
		try
			match s with parser
			| [< '(Comma,_); e = expr >] -> loop (e::acc)
			| [< >] -> List.rev acc
		with Display e ->
			display (ECall (ec,List.rev (e::acc)),punion (pos ec) (pos e))
	in
	match e with
	| None -> []
	| Some e -> loop [e]

and parse_macro_cond allow_op s =
	match s with parser
	| [< '(Const (Ident t),p) >] ->
		parse_macro_ident allow_op t p s
	| [< '(Const (String s),p) >] ->
		None, (EConst (String s),p)
	| [< '(Const (Int i),p) >] ->
		None, (EConst (Int i),p)
	| [< '(Const (Float f),p) >] ->
		None, (EConst (Float f),p)
	| [< '(Kwd k,p) >] ->
		parse_macro_ident allow_op (s_keyword k) p s
	| [< '(POpen, p1); _,e = parse_macro_cond true; '(PClose, p2) >] ->
		let e = (EParenthesis e,punion p1 p2) in
		if allow_op then parse_macro_op e s else None, e
	| [< '(Unop op,p); tk, e = parse_macro_cond allow_op >] ->
		tk, make_unop op e p

and parse_macro_ident allow_op t p s =
	let e = (EConst (Ident t),p) in
	if not allow_op then
		None, e
	else
		parse_macro_op e s

and parse_macro_op e s =
	match Stream.peek s with
	| Some (Binop op,_) ->
		Stream.junk s;
		let op = match Stream.peek s with
			| Some (Binop OpAssign,_) when op = OpGt ->
				Stream.junk s;
				OpGte
			| _ -> op
		in
		let tk, e2 = (try parse_macro_cond true s with Stream.Failure -> serror()) in
		tk, make_binop op e e2
	| tk ->
		tk, e

and toplevel_expr s =
	try
		expr s
	with
		Display e -> e

and secure_expr = parser
	| [< e = expr >] -> e
	| [< >] -> serror()

(* eval *)
type small_type =
	| TNull
	| TBool of bool
	| TFloat of float
	| TString of string

let is_true = function
	| TBool false | TNull | TFloat 0. | TString "" -> false
	| _ -> true

let cmp v1 v2 =
	match v1, v2 with
	| TNull, TNull -> 0
	| TFloat a, TFloat b -> compare a b
	| TString a, TString b -> compare a b
	| TBool a, TBool b -> compare a b
	| TString a, TFloat b -> compare (float_of_string a) b
	| TFloat a, TString b -> compare a (float_of_string b)
	| _ -> raise Exit (* always false *)

let rec eval ctx (e,p) =
	match e with
	| EConst (Ident i) ->
		(try TString (Common.raw_defined_value ctx i) with Not_found -> TNull)
	| EConst (String s) -> TString s
	| EConst (Int i) -> TFloat (float_of_string i)
	| EConst (Float f) -> TFloat (float_of_string f)
	| EBinop (OpBoolAnd, e1, e2) -> TBool (is_true (eval ctx e1) && is_true (eval ctx e2))
	| EBinop (OpBoolOr, e1, e2) -> TBool (is_true (eval ctx e1) || is_true(eval ctx e2))
	| EUnop (Not, _, e) -> TBool (not (is_true (eval ctx e)))
	| EParenthesis e -> eval ctx e
	| EBinop (op, e1, e2) ->
		let v1 = eval ctx e1 in
		let v2 = eval ctx e2 in
		let compare op =
			TBool (try op (cmp v1 v2) 0 with _ -> false)
		in
		(match op with
		| OpEq -> compare (=)
		| OpNotEq -> compare (<>)
		| OpGt -> compare (>)
		| OpGte -> compare (>=)
		| OpLt -> compare (<)
		| OpLte -> compare (<=)
		| _ -> error (Custom "Unsupported operation") p)
	| _ ->
		error (Custom "Invalid condition expression") p

(* parse main *)
let parse ctx code =
	let old = Lexer.save() in
	let old_cache = !cache in
	let mstack = ref [] in
	let old_use_extended_syntax = !use_extended_syntax in
	let old_for_ctx = !for_ctx in
	cache := DynArray.create();
	last_doc := None;
	in_macro := Common.defined ctx Common.Define.Macro;
	use_extended_syntax := ctx.Common.use_extended_syntax || Common.defined ctx Common.Define.UseExtendedSyntax;
	warning := ctx.Common.warning;
	for_ctx := [];
	Lexer.skip_header code;

	let sraw = Stream.from (fun _ -> Some (Lexer.token code)) in
	let rec next_token() = process_token (Lexer.token code)

	and process_token tk =
		match fst tk with
		| Comment s ->
			let tk = next_token() in
			if !use_doc then begin
				let l = String.length s in
				if l > 0 && s.[0] = '*' then last_doc := Some (String.sub s 1 (l - (if l > 1 && s.[l-1] = '*' then 2 else 1)), (snd tk).pmin);
			end;
			tk
		| CommentLine s ->
			next_token()
		| Sharp "end" ->
			(match !mstack with
			| [] -> tk
			| _ :: l ->
				mstack := l;
				next_token())
		| Sharp "else" | Sharp "elseif" ->
			(match !mstack with
			| [] -> tk
			| _ :: l ->
				mstack := l;
				process_token (skip_tokens (snd tk) false))
		| Sharp "if" ->
			process_token (enter_macro (snd tk))
		| Sharp "error" ->
			(match Lexer.token code with
			| (Const (String s),p) -> error (Custom s) p
			| _ -> error Unimplemented (snd tk))
		| Sharp "line" ->
			let line = (match next_token() with
				| (Const (Int s),_) -> int_of_string s
				| (t,p) -> error (Unexpected t) p
			) in
			!(Lexer.cur).Lexer.lline <- line - 1;
			next_token();
		| _ ->
			tk

	and enter_macro p =
		let tk, e = parse_macro_cond false sraw in
		let tk = (match tk with None -> Lexer.token code | Some tk -> tk) in
		if is_true (eval ctx e) || (match fst e with EConst (Ident "macro") when Common.unique_full_path p.pfile = (!resume_display).pfile -> true | _ -> false) then begin
			mstack := p :: !mstack;
			tk
		end else
			skip_tokens_loop p true tk

	and skip_tokens_loop p test tk =
		match fst tk with
		| Sharp "end" ->
			Lexer.token code
		| Sharp "elseif" | Sharp "else" when not test ->
			skip_tokens p test
		| Sharp "else" ->
			mstack := snd tk :: !mstack;
			Lexer.token code
		| Sharp "elseif" ->
			enter_macro (snd tk)
		| Sharp "if" ->
			skip_tokens_loop p test (skip_tokens p false)
		| Eof ->
			if do_resume() then tk else error Unclosed_macro p
		| _ ->
			skip_tokens p test

	and skip_tokens p test = skip_tokens_loop p test (Lexer.token code)

	in
	let s = Stream.from (fun _ ->
		let t = next_token() in
		DynArray.add (!cache) t;
		Some t
	) in
	try
		let l = parse_file s in
		(match !mstack with p :: _ when not (do_resume()) -> error Unclosed_macro p | _ -> ());
		cache := old_cache;
		use_extended_syntax := old_use_extended_syntax;
		for_ctx := old_for_ctx;
		Lexer.restore old;
		l
	with
		| Stream.Error _
		| Stream.Failure ->
			let last = (match Stream.peek s with None -> last_token s | Some t -> t) in
			Lexer.restore old;
			cache := old_cache;
			use_extended_syntax := old_use_extended_syntax;
			for_ctx := old_for_ctx;
			error (Unexpected (fst last)) (pos last)
		| e ->
			Lexer.restore old;
			cache := old_cache;
			use_extended_syntax := old_use_extended_syntax;
			for_ctx := old_for_ctx;
			raise e
