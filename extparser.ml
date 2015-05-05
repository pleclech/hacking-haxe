open Ast

let use_extended_syntax = ref false

let mk_efield e n p = EField (e, n), p
let mk_eblock b p = EBlock b, p
let mk_eident n p = (EConst(Ident n), p)
let mk_estring n p = (EConst(String n), p)
let mk_eint i p = (EConst(Int (string_of_int i)), p)

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
