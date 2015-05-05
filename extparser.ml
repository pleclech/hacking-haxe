open Ast

let use_extended_syntax = ref false

let warning : (string -> pos -> unit) ref = ref (fun _ _ -> assert false)

let mk_efield e n p = EField (e, n), p
let mk_eblock b p = EBlock b, p
let mk_eident n p = (EConst(Ident n), p)
let mk_estring n p = (EConst(String n), p)
let mk_eint i p = (EConst(Int (string_of_int i)), p)
let mk_mconst p = (Meta.Const, [], p)

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

let val_or_const = parser
	| [< '(Kwd Val,p) >] -> "val", p
	| [< '(Kwd KConst,p) >] -> "const", p

let add_parsed_const meta s =
	let sp = const_pos s in
	match  sp with
	| Some p ->
		Stream.junk s;
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



