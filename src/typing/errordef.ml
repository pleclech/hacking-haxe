
open Typedef

open Typeunifyerror


type call_error =
	| Not_enough_arguments of (string * bool * t) list
	| Too_many_arguments
	| Could_not_unify of error_msg
	| Cannot_skip_non_nullable of string

and error_msg =
	| Module_not_found of path
	| Type_not_found of path * string
	| Unify of unify_error list
	| Custom of string
	| Unknown_ident of string
	| Stack of error_msg * error_msg
	| Call_error of call_error
	| No_constructor of module_type

exception Fatal_error of string * Globals.pos
exception Error of error_msg * Globals.pos

