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
open Globals

type path = string list * string

type field_kind =
	| Var of var_kind
	| Method of method_kind

and var_kind = {
	v_read : var_access;
	v_write : var_access;
}

and var_access =
	| AccNormal
	| AccNo				(* can't be accessed outside of the class itself and its subclasses *)
	| AccNever			(* can't be accessed, even in subclasses *)
	| AccResolve		(* call resolve("field") when accessed *)
	| AccCall			(* perform a method call when accessed *)
	| AccInline			(* similar to Normal but inline when accessed *)
	| AccRequire of string * string option (* set when @:require(cond) fails *)

and method_kind =
	| MethNormal
	| MethInline
	| MethDynamic
	| MethMacro

type module_check_policy =
	| NoCheckFileTimeModification
	| CheckFileContentModification
	| NoCheckDependencies
	| NoCheckShadowing

type t =
	| TMono of t option ref
	| TEnum of tenum * tparams
	| TInst of tclass * tparams
	| TType of tdef * tparams
	| TFun of tsignature
	| TAnon of tanon
	| TDynamic of t
	| TLazy of (unit -> t) ref
	| TAbstract of tabstract * tparams

and tsignature = (string * bool * t) list * t

and tparams = t list

and type_params = (string * t) list

and tconstant =
	| TInt of int32
	| TFloat of string
	| TString of string
	| TBool of bool
	| TNull
	| TThis
	| TSuper

and tvar_extra = (type_params * texpr option) option

and tvar = {
	mutable v_id : int;
	mutable v_name : string;
	mutable v_type : t;
	mutable v_capture : bool;
	mutable v_extra : tvar_extra;
	mutable v_meta : metadata;
	v_pos : pos;
}

and tfunc = {
	tf_args : (tvar * tconstant option) list;
	tf_type : t;
	tf_expr : texpr;
}

and anon_status =
	| Closed
	| Opened
	| Const
	| Extend of t list
	| Statics of tclass
	| EnumStatics of tenum
	| AbstractStatics of tabstract

and tanon = {
	mutable a_fields : (string, tclass_field) PMap.t;
	a_status : anon_status ref;
}

and texpr_expr =
	| TConst of tconstant
	| TLocal of tvar
	| TArray of texpr * texpr
	| TBinop of Ast.binop * texpr * texpr
	| TField of texpr * tfield_access
	| TTypeExpr of module_type
	| TParenthesis of texpr
	| TObjectDecl of (string * texpr) list
	| TArrayDecl of texpr list
	| TCall of texpr * texpr list
	| TNew of tclass * tparams * texpr list
	| TUnop of Ast.unop * Ast.unop_flag * texpr
	| TFunction of tfunc
	| TVar of tvar * texpr option
	| TBlock of texpr list
	| TFor of tvar * texpr * texpr
	| TIf of texpr * texpr * texpr option
	| TWhile of texpr * texpr * Ast.while_flag
	| TSwitch of texpr * (texpr list * texpr) list * texpr option
	| TTry of texpr * (tvar * texpr) list
	| TReturn of texpr option
	| TBreak
	| TContinue
	| TThrow of texpr
	| TCast of texpr * module_type option
	| TMeta of metadata_entry * texpr
	| TEnumParameter of texpr * tenum_field * int

and tfield_access =
	| FInstance of tclass * tparams * tclass_field
	| FStatic of tclass * tclass_field
	| FAnon of tclass_field
	| FDynamic of string
	| FClosure of (tclass * tparams) option * tclass_field (* None class = TAnon *)
	| FEnum of tenum * tenum_field

and texpr = {
	eexpr : texpr_expr;
	etype : t;
	epos : pos;
}

and tclass_field = {
	mutable cf_name : string;
	mutable cf_type : t;
	mutable cf_public : bool;
	cf_pos : pos;
	cf_name_pos : pos;
	mutable cf_doc : Ast.documentation;
	mutable cf_meta : metadata;
	mutable cf_kind : field_kind;
	mutable cf_params : type_params;
	mutable cf_expr : texpr option;
	mutable cf_expr_unoptimized : tfunc option;
	mutable cf_overloads : tclass_field list;
	mutable cf_override : tclass_field option;
}

and tclass_kind =
	| KNormal
	| KTypeParameter of t list
	| KExpr of Ast.expr
	| KGeneric
	| KGenericInstance of tclass * tparams
	| KMacroType
	| KGenericBuild of class_field list
	| KAbstractImpl of tabstract

and metadata = Ast.metadata

and tinfos = {
	mt_path : path;
	mt_module : module_def;
	mt_pos : pos;
	mt_name_pos : pos;
	mt_private : bool;
	mt_doc : Ast.documentation;
	mutable mt_meta : metadata;
	mt_params : type_params;
}

and tclass = {
	mutable cl_path : path;
	mutable cl_module : module_def;
	mutable cl_pos : pos;
	mutable cl_name_pos : pos;
	mutable cl_private : bool;
	mutable cl_doc : Ast.documentation;
	mutable cl_meta : metadata;
	mutable cl_params : type_params;
	(* do not insert any fields above *)
	mutable cl_kind : tclass_kind;
	mutable cl_extern : bool;
	mutable cl_interface : bool;
	mutable cl_super : (tclass * tparams) option;
	mutable cl_implements : (tclass * tparams) list;
	mutable cl_fields : (string, tclass_field) PMap.t;
	mutable cl_statics : (string, tclass_field) PMap.t;
	mutable cl_ordered_statics : tclass_field list;
	mutable cl_ordered_fields : tclass_field list;
	mutable cl_dynamic : t option;
	mutable cl_array_access : t option;
	mutable cl_constructor : tclass_field option;
	mutable cl_init : texpr option;
	mutable cl_overrides : tclass_field list;

	mutable cl_build : unit -> build_state;
	mutable cl_restore : unit -> unit;
	(*
		These are classes which directly extend or directly implement this class.
		Populated automatically in post-processing step (Filters.run)
	*)
	mutable cl_descendants : tclass list;
}

and tenum_field = {
	ef_name : string;
	ef_type : t;
	ef_pos : pos;
	ef_name_pos : pos;
	ef_doc : Ast.documentation;
	ef_index : int;
	ef_params : type_params;
	mutable ef_meta : metadata;
}

and tenum = {
	mutable e_path : path;
	e_module : module_def;
	e_pos : pos;
	e_name_pos : pos;
	e_private : bool;
	e_doc : Ast.documentation;
	mutable e_meta : metadata;
	mutable e_params : type_params;
	(* do not insert any fields above *)
	e_type : tdef;
	mutable e_extern : bool;
	mutable e_constrs : (string , tenum_field) PMap.t;
	mutable e_names : string list;
}

and tdef = {
	t_path : path;
	t_module : module_def;
	t_pos : pos;
	t_name_pos : pos;
	t_private : bool;
	t_doc : Ast.documentation;
	mutable t_meta : metadata;
	mutable t_params : type_params;
	(* do not insert any fields above *)
	mutable t_type : t;
}

and tabstract = {
	mutable a_path : path;
	a_module : module_def;
	a_pos : pos;
	a_name_pos : pos;
	a_private : bool;
	a_doc : Ast.documentation;
	mutable a_meta : metadata;
	mutable a_params : type_params;
	(* do not insert any fields above *)
	mutable a_ops : (Ast.binop * tclass_field) list;
	mutable a_unops : (Ast.unop * unop_flag * tclass_field) list;
	mutable a_impl : tclass option;
	mutable a_this : t;
	mutable a_from : t list;
	mutable a_from_field : (t * tclass_field) list;
	mutable a_to : t list;
	mutable a_to_field : (t * tclass_field) list;
	mutable a_array : tclass_field list;
	mutable a_resolve : tclass_field option;
}

and module_type =
	| TClassDecl of tclass
	| TEnumDecl of tenum
	| TTypeDecl of tdef
	| TAbstractDecl of tabstract

and module_def = {
	m_id : int;
	m_path : path;
	mutable m_types : module_type list;
	m_extra : module_def_extra;
}

and module_def_extra = {
	m_file : string;
	m_sign : string;
	mutable m_check_policy : module_check_policy list;
	mutable m_time : float;
	mutable m_dirty : module_def option;
	mutable m_added : int;
	mutable m_mark : int;
	mutable m_deps : (int,module_def) PMap.t;
	mutable m_processed : int;
	mutable m_kind : module_kind;
	mutable m_binded_res : (string, string) PMap.t;
	mutable m_macro_calls : string list;
	mutable m_if_feature : (string *(tclass * tclass_field * bool)) list;
	mutable m_features : (string,bool) Hashtbl.t;
}

and module_kind =
	| MCode
	| MMacro
	| MFake
	| MSub
	| MExtern
	| MImport

and build_state =
	| Built
	| Building of tclass list
	| BuildMacro of (unit -> unit) list ref

