open Ast
open Globals
open Typedef

open Typecoredef

let unavailable = ref []
let factories = ref []

let register_factory name factory = factories := (name,factory) :: !factories

let re = Str.regexp "^\\([a-zA-Z_]+\\)\\([0-9]+\\)?$"

let find_type_factory s = List.find(fun (name,factory) -> name=s) !factories

let get_arity s =
    ignore(Str.search_forward re s 0);
	let i = try int_of_string (Str.matched_group 2 s) with Not_found -> -1 in
	let n = Str.matched_group 1 s in
	n, i

let get_create_factory tname =
    let n,i = get_arity tname in
	let n,tf = find_type_factory n in
	n,i,tf

let create_type ctx tname error (type_module:typer -> path -> string -> type_decl list -> pos -> module_def) =
	if List.exists (fun n -> n=tname) !unavailable then error()
	else try
		let name, arity, factory = get_create_factory tname in
		let s = factory tname name arity in
		let (_,decls), cn, p = Typeutils.create_type tname ctx.Typecoredef.com s in
		type_module ctx ([], cn) p.pfile decls p
	with Not_found ->
		unavailable := tname :: !unavailable;
		error()
