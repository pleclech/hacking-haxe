(*
	The Haxe Compiler
	Copyright (C) 2005-2017  Haxe Foundation

	This program is free software; you can redistribute it and/or
	modify it under the terms of the GNU General Public License
	as published by the Free Software Foundation; either version 2
	of the License, or (at your option) any later version.

	This program is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with this program; if not, write to the Free Software
	Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA.
 *)




open Ast
open Common
open Typedef
open Typeutility


open Errordef
open Error

type with_type =
	| NoValue
	| Value
	| WithType of t

type type_patch = {
	mutable tp_type : complex_type option;
	mutable tp_remove : bool;
	mutable tp_meta : metadata;
}

type current_fun =
	| FunMember
	| FunStatic
	| FunConstructor
	| FunMemberAbstract
	| FunMemberClassLocal
	| FunMemberAbstractLocal

type macro_mode =
	| MExpr
	| MBuild
	| MMacroType
	| MDisplay

type typer_pass =
	| PBuildModule			(* build the module structure and setup module type parameters *)
	| PBuildClass			(* build the class structure *)
	| PTypeField			(* type the class field, allow access to types structures *)
	| PCheckConstraint		(* perform late constraint checks with inferred types *)
	| PForce				(* usually ensure that lazy have been evaluated *)
	| PFinal				(* not used, only mark for finalize *)

type typer_module = {
	curmod : module_def;
	mutable module_types : (module_type * pos) list;
	mutable module_using : (tclass * pos) list;
	mutable module_globals : (string, (module_type * string * pos)) PMap.t;
	mutable wildcard_packages : (string list * pos) list;
	mutable module_imports : import list;
}

type typer_globals = {
	types_module : (path, path) Hashtbl.t;
	modules : (path , module_def) Hashtbl.t;
	mutable delayed : (typer_pass * (unit -> unit) list) list;
	mutable debug_delayed : (typer_pass * ((unit -> unit) * string * typer) list) list;
	doinline : bool;
	mutable core_api : typer option;
	mutable macros : ((unit -> unit) * typer) option;
	mutable std : module_def;
	mutable hook_generate : (unit -> unit) list;
	type_patches : (path, (string * bool, type_patch) Hashtbl.t * type_patch) Hashtbl.t;
	mutable global_metadata : (string list * metadata_entry * (bool * bool * bool)) list;
	mutable module_check_policies : (string list * module_check_policy list * bool) list;
	mutable get_build_infos : unit -> (module_type * t list * class_field list) option;
	delayed_macros : (unit -> unit) DynArray.t;
	mutable global_using : (tclass * pos) list;
	(* api *)
	do_inherit : typer -> Typedef.tclass -> pos -> (bool * placed_type_path) -> bool;
	do_create : Common.context -> typer;
	do_macro : typer -> macro_mode -> path -> string -> expr list -> pos -> expr option;
	do_load_module : typer -> path -> pos -> module_def;
	do_optimize : typer -> texpr -> texpr;
	do_build_instance : typer -> module_type -> pos -> ((string * t) list * path * (t list -> t));
	do_format_string : typer -> string -> pos -> Ast.expr;
	do_finalize : typer -> unit;
	do_generate : typer -> (texpr option * module_type list * module_def list);
}

and typer = {
	(* shared *)
	com : context;
	t : basic_types;
	g : typer_globals;
	mutable meta : metadata;
	mutable this_stack : texpr list;
	mutable with_type_stack : with_type list;
	mutable call_argument_stack : expr list list;
	(* variable *)
	mutable pass : typer_pass;
	(* per-module *)
	mutable m : typer_module;
	mutable is_display_file : bool;
	(* per-class *)
	mutable curclass : tclass;
	mutable tthis : t;
	mutable type_params : (string * t) list;
	(* per-function *)
	mutable curfield : tclass_field;
	mutable untyped : bool;
	mutable in_loop : bool;
	mutable in_display : bool;
	mutable in_macro : bool;
	mutable macro_depth : int;
	mutable curfun : current_fun;
	mutable ret : t;
	mutable locals : (string, tvar) PMap.t;
	mutable opened : anon_status ref list;
	mutable vthis : tvar option;
	mutable in_call_args : bool;
	(* events *)
	mutable on_error : typer -> string -> pos -> unit;
}
exception Forbid_package of (string * path * pos) * pos list * string

exception WithTypeError of error_msg * pos

let make_call_ref : (typer -> texpr -> texpr list -> t -> pos -> texpr) ref = ref (fun _ _ _ _ _ -> assert false)
let type_expr_ref : (typer -> expr -> with_type -> texpr) ref = ref (fun _ _ _ -> assert false)
let type_module_type_ref : (typer -> module_type -> t list option -> pos -> texpr) ref = ref (fun _ _ _ _ -> assert false)
let unify_min_ref : (typer -> texpr list -> t) ref = ref (fun _ _ -> assert false)
let match_expr_ref : (typer -> expr -> (expr list * expr option * expr option * pos) list -> (expr option * pos) option -> with_type -> pos -> texpr) ref = ref (fun _ _ _ _ _ _ -> assert false)
let get_pattern_locals_ref : (typer -> expr -> Typedef.t -> (string, tvar * pos) PMap.t) ref = ref (fun _ _ _ -> assert false)
let get_constructor_ref : (typer -> tclass -> t list -> pos -> (t * tclass_field)) ref = ref (fun _ _ _ _ -> assert false)
let cast_or_unify_ref : (typer -> t -> texpr -> pos -> texpr) ref = ref (fun _ _ _ _ -> assert false)
let find_array_access_raise_ref : (typer -> tabstract -> tparams -> texpr -> texpr option -> pos -> (tclass_field * t * t * texpr * texpr option)) ref = ref (fun _ _ _ _ _ _ -> assert false)
let analyzer_run_on_expr_ref : (Common.context -> texpr -> texpr) ref = ref (fun _ _ -> assert false)
let merge_core_doc_ref : (typer -> tclass -> unit) ref = ref (fun _ _ -> assert false)

let pass_name = function
	| PBuildModule -> "build-module"
	| PBuildClass -> "build-class"
	| PTypeField -> "type-field"
	| PCheckConstraint -> "check-constraint"
	| PForce -> "force"
	| PFinal -> "final"

let display_error ctx msg p = match ctx.com.display.DisplayMode.dms_error_policy with
	| DisplayMode.EPShow | DisplayMode.EPIgnore -> ctx.on_error ctx msg p
	| DisplayMode.EPCollect -> add_diagnostics_message ctx.com msg p DisplayTypes.DiagnosticsSeverity.Error

let make_call ctx e el t p = (!make_call_ref) ctx e el t p

let type_expr ctx e with_type = (!type_expr_ref) ctx e with_type

let unify_min ctx el = (!unify_min_ref) ctx el

let match_expr ctx e cases def with_type p = !match_expr_ref ctx e cases def with_type p

let make_static_this c p =
	let ta = TAnon { a_fields = c.cl_statics; a_status = ref (Statics c) } in
	mk (TTypeExpr (TClassDecl c)) ta p

let make_static_field_access c cf t p =
	let ethis = make_static_this c p in
	mk (TField (ethis,(FStatic (c,cf)))) t p

let make_static_call ctx c cf map args t p =
	let monos = List.map (fun _ -> mk_mono()) cf.cf_params in
	let map t = map (apply_params cf.cf_params monos t) in
	let ef = make_static_field_access c cf (map cf.cf_type) p in
	make_call ctx ef args (map t) p

let raise_or_display ctx l p =
	if ctx.untyped then ()
	else if ctx.in_call_args then raise (WithTypeError(Unify l,p))
	else display_error ctx (error_msg (Unify l)) p

let raise_or_display_message ctx msg p =
	if ctx.in_call_args then raise (WithTypeError (Custom msg,p))
	else display_error ctx msg p

