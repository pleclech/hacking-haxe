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
open Typedef
open Typeutility

(* ======= Unification ======= *)

let rec link e a b =
	(* tell if setting a == b will create a type-loop *)
	let rec loop t =
		if t == a then
			true
		else match t with
		| TMono t -> (match !t with None -> false | Some t -> loop t)
		| TEnum (_,tl) -> List.exists loop tl
		| TInst (_,tl) | TType (_,tl) | TAbstract (_,tl) -> List.exists loop tl
		| TFun (tl,t) -> List.exists (fun (_,_,t) -> loop t) tl || loop t
		| TDynamic t2 ->
			if t == t2 then
				false
			else
				loop t2
		| TLazy f ->
			loop (!f())
		| TAnon a ->
			try
				PMap.iter (fun _ f -> if loop f.cf_type then raise Exit) a.a_fields;
				false
			with
				Exit -> true
	in
	(* tell is already a ~= b *)
	if loop b then
		(follow b) == a
	else if b == t_dynamic then
		true
	else begin
		e := Some b;
		true
	end

let link_dynamic a b = match follow a,follow b with
	| TMono r,TDynamic _ -> r := Some b
	| TDynamic _,TMono r -> r := Some a
	| _ -> ()

let rec fast_eq a b =
	if a == b then
		true
	else match a , b with
	| TFun (l1,r1) , TFun (l2,r2) when List.length l1 = List.length l2 ->
		List.for_all2 (fun (_,_,t1) (_,_,t2) -> fast_eq t1 t2) l1 l2 && fast_eq r1 r2
	| TType (t1,l1), TType (t2,l2) ->
		t1 == t2 && List.for_all2 fast_eq l1 l2
	| TEnum (e1,l1), TEnum (e2,l2) ->
		e1 == e2 && List.for_all2 fast_eq l1 l2
	| TInst (c1,l1), TInst (c2,l2) ->
		c1 == c2 && List.for_all2 fast_eq l1 l2
	| TAbstract (a1,l1), TAbstract (a2,l2) ->
		a1 == a2 && List.for_all2 fast_eq l1 l2
	| _ , _ ->
		false

let rec fast_eq_mono ml a b =
	if a == b then
		true
	else match a , b with
	| TFun (l1,r1) , TFun (l2,r2) when List.length l1 = List.length l2 ->
		List.for_all2 (fun (_,_,t1) (_,_,t2) -> fast_eq_mono ml t1 t2) l1 l2 && fast_eq_mono ml r1 r2
	| TType (t1,l1), TType (t2,l2) ->
		t1 == t2 && List.for_all2 (fast_eq_mono ml) l1 l2
	| TEnum (e1,l1), TEnum (e2,l2) ->
		e1 == e2 && List.for_all2 (fast_eq_mono ml) l1 l2
	| TInst (c1,l1), TInst (c2,l2) ->
		c1 == c2 && List.for_all2 (fast_eq_mono ml) l1 l2
	| TAbstract (a1,l1), TAbstract (a2,l2) ->
		a1 == a2 && List.for_all2 (fast_eq_mono ml) l1 l2
	| TMono _, _ ->
		List.memq a ml
	| _ , _ ->
		false

(* perform unification with subtyping.
   the first type is always the most down in the class hierarchy
   it's also the one that is pointed by the position.
   It's actually a typecheck of  A :> B where some mutations can happen *)



open Typeunifyerror


let has_meta m ml = List.exists (fun (m2,_,_) -> m = m2) ml
let get_meta m ml = List.find (fun (m2,_,_) -> m = m2) ml
let no_meta = []

(*
	we can restrict access as soon as both are runtime-compatible
*)
let unify_access a1 a2 =
	a1 = a2 || match a1, a2 with
	| _, AccNo | _, AccNever -> true
	| AccInline, AccNormal -> true
	| _ -> false

let direct_access = function
	| AccNo | AccNever | AccNormal | AccInline | AccRequire _ -> true
	| AccResolve | AccCall -> false

let unify_kind k1 k2 =
	k1 = k2 || match k1, k2 with
		| Var v1, Var v2 -> unify_access v1.v_read v2.v_read && unify_access v1.v_write v2.v_write
		| Var v, Method m ->
			(match v.v_read, v.v_write, m with
			| AccNormal, _, MethNormal -> true
			| AccNormal, AccNormal, MethDynamic -> true
			| _ -> false)
		| Method m, Var v ->
			(match m with
			| MethDynamic -> direct_access v.v_read && direct_access v.v_write
			| MethMacro -> false
			| MethNormal | MethInline ->
				match v.v_read,v.v_write with
				| AccNormal,(AccNo | AccNever) -> true
				| _ -> false)
		| Method m1, Method m2 ->
			match m1,m2 with
			| MethInline, MethNormal
			| MethDynamic, MethNormal -> true
			| _ -> false

let eq_stack = ref []

type eq_kind =
	| EqStrict
	| EqCoreType
	| EqRightDynamic
	| EqBothDynamic
	| EqDoNotFollowNull (* like EqStrict, but does not follow Null<T> *)

let rec type_eq param a b =
	let can_follow t = match param with
		| EqCoreType -> false
		| EqDoNotFollowNull -> not (is_explicit_null t)
		| _ -> true
	in
	if a == b then
		()
	else match a , b with
	| TLazy f , _ -> type_eq param (!f()) b
	| _ , TLazy f -> type_eq param a (!f())
	| TMono t , _ ->
		(match !t with
		| None -> if param = EqCoreType || not (link t a b) then error [cannot_unify a b]
		| Some t -> type_eq param t b)
	| _ , TMono t ->
		(match !t with
		| None -> if param = EqCoreType || not (link t b a) then error [cannot_unify a b]
		| Some t -> type_eq param a t)
	| TAbstract(a1, [a]), TAbstract(a2, [b]) when Higherkind.is_in a1.a_meta && Higherkind.is_in a2.a_meta ->
		(try type_eq param a b with Unify_error _ -> ())
	| TAbstract(a1, [a]), _ when Higherkind.is_in a1.a_meta -> ()
	| _, TAbstract(a2, [b]) when Higherkind.is_in a2.a_meta -> ()
	| TType (t1,tl1), TType (t2,tl2) when (t1 == t2 || (param = EqCoreType && t1.t_path = t2.t_path)) && List.length tl1 = List.length tl2 ->
		List.iter2 (type_eq param) tl1 tl2
	| TType (t,tl) , _ when can_follow a ->
		type_eq param (apply_params t.t_params tl t.t_type) b
	| _ , TType (t,tl) when can_follow b ->
		if List.exists (fun (a2,b2) -> fast_eq a a2 && fast_eq b b2) (!eq_stack) then
			()
		else begin
			eq_stack := (a,b) :: !eq_stack;
			try
				type_eq param a (apply_params t.t_params tl t.t_type);
				eq_stack := List.tl !eq_stack;
			with
				Unify_error l ->
					eq_stack := List.tl !eq_stack;
					error (cannot_unify a b :: l)
		end
	| TEnum (e1,tl1) , TEnum (e2,tl2) ->
		if e1 != e2 && not (param = EqCoreType && e1.e_path = e2.e_path) then error [cannot_unify a b];
		List.iter2 (type_eq param) tl1 tl2
	| TInst (c1,tl1) , TInst (c2,tl2) ->
		if c1 != c2 && not (param = EqCoreType && c1.cl_path = c2.cl_path) && (match c1.cl_kind, c2.cl_kind with KExpr _, KExpr _ -> false | _ -> true) then error [cannot_unify a b];
		List.iter2 (type_eq param) tl1 tl2
	| TFun (l1,r1) , TFun (l2,r2) when List.length l1 = List.length l2 ->
		(try
			type_eq param r1 r2;
			List.iter2 (fun (n,o1,t1) (_,o2,t2) ->
				if o1 <> o2 then error [Not_matching_optional n];
				type_eq param t1 t2
			) l1 l2
		with
			Unify_error l -> error (cannot_unify a b :: l))
	| TDynamic a , TDynamic b ->
		type_eq param a b
	| TAbstract (a1,tl1) , TAbstract (a2,tl2) ->
		if a1 != a2 && not (param = EqCoreType && a1.a_path = a2.a_path) then error [cannot_unify a b];
		List.iter2 (type_eq param) tl1 tl2
	| TAnon a1, TAnon a2 ->
		(try
			PMap.iter (fun n f1 ->
				try
					let f2 = PMap.find n a2.a_fields in
					if f1.cf_kind <> f2.cf_kind && (param = EqStrict || param = EqCoreType || not (unify_kind f1.cf_kind f2.cf_kind)) then error [invalid_kind n f1.cf_kind f2.cf_kind];
					let a = f1.cf_type and b = f2.cf_type in
					if not (List.exists (fun (a2,b2) -> fast_eq a a2 && fast_eq b b2) (!eq_stack)) then begin
						eq_stack := (a,b) :: !eq_stack;
						try
							type_eq param a b;
							eq_stack := List.tl !eq_stack;
						with
							Unify_error l ->
								eq_stack := List.tl !eq_stack;
								error (invalid_field n :: l)
					end;
				with
					Not_found ->
						if is_closed a2 then error [has_no_field b n];
						if not (link (ref None) b f1.cf_type) then error [cannot_unify a b];
						a2.a_fields <- PMap.add n f1 a2.a_fields
			) a1.a_fields;
			PMap.iter (fun n f2 ->
				if not (PMap.mem n a1.a_fields) then begin
					if is_closed a1 then error [has_no_field a n];
					if not (link (ref None) a f2.cf_type) then error [cannot_unify a b];
					a1.a_fields <- PMap.add n f2 a1.a_fields
				end;
			) a2.a_fields;
		with
			Unify_error l -> error (cannot_unify a b :: l))
	| _ , _ ->
		if b == t_dynamic && (param = EqRightDynamic || param = EqBothDynamic) then
			()
		else if a == t_dynamic && param = EqBothDynamic then
			()
		else
			error [cannot_unify a b]

let type_iseq a b =
	try
		type_eq EqStrict a b;
		true
	with
		Unify_error _ -> false

let type_iseq_strict a b =
	try
		type_eq EqDoNotFollowNull a b;
		true
	with Unify_error _ ->
		false

let unify_stack = ref []
let abstract_cast_stack = ref []
let unify_new_monos = ref []

let print_stacks() =
	let ctx = print_context() in
	let st = s_type ctx in
	print_endline "unify_stack";
	List.iter (fun (a,b) -> Printf.printf "\t%s , %s\n" (st a) (st b)) !unify_stack;
	print_endline "monos";
	List.iter (fun m -> print_endline ("\t" ^ st m)) !unify_new_monos;
	print_endline "abstract_cast_stack";
	List.iter (fun (a,b) -> Printf.printf "\t%s , %s\n" (st a) (st b)) !abstract_cast_stack

let rec unify ?(ignoreInError=false) a b =
	if a == b then
		()
	else match a, b with
	| TLazy f , _ -> unify (!f()) b
	| _ , TLazy f -> unify a (!f())
	| TMono t , _ ->
		(match !t with
		| None -> if not (link t a b) then error [cannot_unify a b]
		| Some t -> unify t b)
	| _ , TMono t ->
		(match !t with
		| None -> if not (link t b a) then error [cannot_unify a b]
		| Some t -> unify a t)
	| TAbstract(a1, [a]), TAbstract(a2, [b]) when Higherkind.is_in a1.a_meta && Higherkind.is_in a2.a_meta ->
		(try unify a b with Unify_error _ as e -> if not ignoreInError then raise e else ())
	| TAbstract(a1, [a]), _ when Higherkind.is_in a1.a_meta ->
		(try unify a b with Unify_error _ as e -> if not ignoreInError then raise e else ())
	| _, TAbstract(a2, [b]) when Higherkind.is_in a2.a_meta ->
		(try unify a b with Unify_error _ as e -> if not ignoreInError then raise e else ())
	| TAbstract(a1, tl1), TAbstract(a2, tl2) when Higherkind.is_hkt a1.a_meta && Higherkind.is_hkt a2.a_meta ->
		let c1,cins1,ctl1 = Higherkind.fill_with_abstract a1 tl1 in
		let c2,cins2,ctl2 = Higherkind.fill_with_abstract a2 tl2 in
		unify c1 c2;
		List.iter2 (fun t1 t2 -> unify ~ignoreInError:true t1 t2) ctl1 ctl2;
		Higherkind.erase_in cins1;
		Higherkind.erase_in cins2
	| TAbstract(a1, tl1), _ when Higherkind.is_hkt a1.a_meta ->
		(try let b = Higherkind.mk_with_abstract2 a1 tl1 b in unify a b with Not_found -> error [cannot_unify a b])
	| _, TAbstract(a2, tl2) when Higherkind.is_hkt a2.a_meta ->
		(try let a = Higherkind.mk_with_abstract2 a2 tl2 a in unify a b with Not_found -> error [cannot_unify a b])
	| TType (t1,tl1), TType (t2,tl2) when t1 == t2 ->
		if not (List.exists (fun (a2,b2) -> fast_eq a a2 && fast_eq b b2) (!unify_stack)) then begin
			try
				unify_stack := (a,b) :: !unify_stack;
				List.iter2 unify tl1 tl2;
				unify_stack := List.tl !unify_stack;
			with
				Unify_error l ->
					unify_stack := List.tl !unify_stack;
					error (cannot_unify a b :: l)
		end
	| TType (t,tl) , _ ->
		if not (List.exists (fun (a2,b2) -> fast_eq a a2 && fast_eq b b2) (!unify_stack)) then begin
			try
				unify_stack := (a,b) :: !unify_stack;
				unify (apply_params t.t_params tl t.t_type) b;
				unify_stack := List.tl !unify_stack;
			with
				Unify_error l ->
					unify_stack := List.tl !unify_stack;
					error (cannot_unify a b :: l)
		end
	| _ , TType (t,tl) ->
		if not (List.exists (fun (a2,b2) -> fast_eq a a2 && fast_eq b b2) (!unify_stack)) then begin
			try
				unify_stack := (a,b) :: !unify_stack;
				unify a (apply_params t.t_params tl t.t_type);
				unify_stack := List.tl !unify_stack;
			with
				Unify_error l ->
					unify_stack := List.tl !unify_stack;
					error (cannot_unify a b :: l)
		end
	| TEnum (ea,tl1) , TEnum (eb,tl2) ->
		if ea != eb then error [cannot_unify a b];
		unify_type_params a b tl1 tl2
	| TAbstract (a1,tl1) , TAbstract (a2,tl2) when a1 == a2 ->
		begin try
			unify_type_params a b tl1 tl2
		with Unify_error _ as err ->
			(* the type could still have a from/to relation to itself (issue #3494) *)
			begin try
				unify_abstracts a b a1 tl1 a2 tl2
			with Unify_error _ ->
				raise err
			end
		end
	| TAbstract ({a_path=[],"Void"},_) , _
	| _ , TAbstract ({a_path=[],"Void"},_) ->
		error [cannot_unify a b]
	| TAbstract (a1,tl1) , TAbstract (a2,tl2) ->
		unify_abstracts a b a1 tl1 a2 tl2
	| TInst (c1,tl1) , TInst (c2,tl2) ->
		let rec loop c tl =
			if c == c2 then begin
				unify_type_params a b tl tl2;
				true
			end else (match c.cl_super with
				| None -> false
				| Some (cs,tls) ->
					loop cs (List.map (apply_params c.cl_params tl) tls)
			) || List.exists (fun (cs,tls) ->
				loop cs (List.map (apply_params c.cl_params tl) tls)
			) c.cl_implements
			|| (match c.cl_kind with
			| KTypeParameter pl -> List.exists (fun t ->
				match follow t with
				| TInst (cs,tls) -> loop cs (List.map (apply_params c.cl_params tl) tls)
				| TAbstract(aa,tl) -> List.exists (unify_to aa tl b) aa.a_to
				| _ -> false
			) pl
			| _ -> false)
		in
		if not (loop c1 tl1) then error [cannot_unify a b]
	| TFun (l1,r1) , TFun (l2,r2) when List.length l1 = List.length l2 ->
		let i = ref 0 in
		(try
			(match r2 with
			| TAbstract ({a_path=[],"Void"},_) -> incr i
			| _ -> unify r1 r2; incr i);
			List.iter2 (fun (_,o1,t1) (_,o2,t2) ->
				if o1 && not o2 then error [Cant_force_optional];
				unify t1 t2;
				incr i
			) l2 l1 (* contravariance *)
		with
			Unify_error l ->
				let msg = if !i = 0 then "Cannot unify return types" else "Cannot unify argument " ^ (string_of_int !i) in
				error (cannot_unify a b :: Unify_custom msg :: l))
	| TInst (c,tl) , TAnon an ->
		if PMap.is_empty an.a_fields then (match c.cl_kind with
			| KTypeParameter pl ->
				(* one of the constraints must unify with { } *)
				if not (List.exists (fun t -> match follow t with TInst _ | TAnon _ -> true | _ -> false) pl) then error [cannot_unify a b]
			| _ -> ());
		(try
			PMap.iter (fun n f2 ->
				(*
					introducing monomorphs while unifying might create infinite loops - see #2315
					let's store these monomorphs and make sure we reach a fixed point
				*)
				let monos = ref [] in
				let make_type f =
					match f.cf_params with
					| [] -> f.cf_type
					| l ->
						let ml = List.map (fun _ -> mk_mono()) l in
						monos := ml;
						apply_params f.cf_params ml f.cf_type
				in
				let _, ft, f1 = (try raw_class_field make_type c tl n with Not_found -> error [has_no_field a n]) in
				let ft = apply_params c.cl_params tl ft in
				if not (unify_kind f1.cf_kind f2.cf_kind) then error [invalid_kind n f1.cf_kind f2.cf_kind];
				if f2.cf_public && not f1.cf_public then error [invalid_visibility n];

				(match f2.cf_kind with
				| Var { v_read = AccNo } | Var { v_read = AccNever } ->
					(* we will do a recursive unification, so let's check for possible recursion *)
					let old_monos = !unify_new_monos in
					unify_new_monos := !monos @ !unify_new_monos;
					if not (List.exists (fun (a2,b2) -> fast_eq b2 f2.cf_type && fast_eq_mono !unify_new_monos ft a2) (!unify_stack)) then begin
						unify_stack := (ft,f2.cf_type) :: !unify_stack;
						(try
							unify_with_access ft f2
						with
							Unify_error l ->
								unify_new_monos := old_monos;
								unify_stack := List.tl !unify_stack;
								error (invalid_field n :: l));
						unify_stack := List.tl !unify_stack;
					end;
					unify_new_monos := old_monos;
				| Method MethNormal | Method MethInline | Var { v_write = AccNo } | Var { v_write = AccNever } ->
					(* same as before, but unification is reversed (read-only var) *)
					let old_monos = !unify_new_monos in
					unify_new_monos := !monos @ !unify_new_monos;
					if not (List.exists (fun (a2,b2) -> fast_eq_mono !unify_new_monos b2 ft && fast_eq f2.cf_type a2) (!unify_stack)) then begin
						unify_stack := (f2.cf_type,ft) :: !unify_stack;
						(try
							unify_with_access ft f2
						with
							Unify_error l ->
								unify_new_monos := old_monos;
								unify_stack := List.tl !unify_stack;
								error (invalid_field n :: l));
						unify_stack := List.tl !unify_stack;
					end;
					unify_new_monos := old_monos;
				| _ ->
					(* will use fast_eq, which have its own stack *)
					try
						unify_with_access ft f2
					with
						Unify_error l ->
							error (invalid_field n :: l));

				List.iter (fun f2o ->
					if not (List.exists (fun f1o -> type_iseq f1o.cf_type f2o.cf_type) (f1 :: f1.cf_overloads))
					then error [Missing_overload (f1, f2o.cf_type)]
				) f2.cf_overloads;
				(* we mark the field as :?used because it might be used through the structure *)
				if not (Meta.has Meta.MaybeUsed f1.cf_meta) then f1.cf_meta <- (Meta.MaybeUsed,[],f1.cf_pos) :: f1.cf_meta;
				(match f1.cf_kind with
				| Method MethInline ->
					if (c.cl_extern || Meta.has Meta.Extern f1.cf_meta) && not (Meta.has Meta.Runtime f1.cf_meta) then error [Has_no_runtime_field (a,n)];
				| _ -> ());
			) an.a_fields;
			(match !(an.a_status) with
			| Opened -> an.a_status := Closed;
			| Statics _ | EnumStatics _ | AbstractStatics _ -> error []
			| Closed | Extend _ | Const -> ())
		with
			Unify_error l -> error (cannot_unify a b :: l))
	| TAnon a1, TAnon a2 ->
		unify_anons a b a1 a2
	| TAnon an, TAbstract ({ a_path = [],"Class" },[pt]) ->
		(match !(an.a_status) with
		| Statics cl -> unify (TInst (cl,List.map (fun _ -> mk_mono()) cl.cl_params)) pt
		| _ -> error [cannot_unify a b])
	| TAnon an, TAbstract ({ a_path = [],"Enum" },[pt]) ->
		(match !(an.a_status) with
		| EnumStatics e -> unify (TEnum (e,List.map (fun _ -> mk_mono()) e.e_params)) pt
		| _ -> error [cannot_unify a b])
	| TEnum _, TAbstract ({ a_path = [],"EnumValue" },[]) ->
		()
	| TEnum(en,_), TAbstract ({ a_path = ["haxe"],"FlatEnum" },[]) when Meta.has Meta.FlatEnum en.e_meta ->
		()
	| TFun _, TAbstract ({ a_path = ["haxe"],"Function" },[]) ->
		()
	| TInst(c,tl),TAbstract({a_path = ["haxe"],"Constructible"},[t1]) ->
		begin try
			begin match c.cl_kind with
				| KTypeParameter tl ->
					(* type parameters require an equal Constructible constraint *)
					if not (List.exists (fun t -> match follow t with TAbstract({a_path = ["haxe"],"Constructible"},[t2]) -> type_iseq t1 t2 | _ -> false) tl) then error [cannot_unify a b]
				| _ ->
					let _,t,cf = class_field c tl "new" in
					if not cf.cf_public then error [invalid_visibility "new"];
					begin try unify t1 t
					with Unify_error l -> error (cannot_unify a b :: l) end
			end
		with Not_found ->
			error [has_no_field a "new"]
		end
	| TDynamic t , _ ->
		if t == a then
			()
		else (match b with
		| TDynamic t2 ->
			if t2 != b then
				(try
					type_eq EqRightDynamic t t2
				with
					Unify_error l -> error (cannot_unify a b :: l));
		| TAbstract(bb,tl) when (List.exists (unify_from bb tl a b) bb.a_from) ->
			()
		| _ ->
			error [cannot_unify a b])
	| _ , TDynamic t ->
		if t == b then
			()
		else (match a with
		| TDynamic t2 ->
			if t2 != a then
				(try
					type_eq EqRightDynamic t t2
				with
					Unify_error l -> error (cannot_unify a b :: l));
		| TAnon an ->
			(try
				(match !(an.a_status) with
				| Statics _ | EnumStatics _ -> error []
				| Opened -> an.a_status := Closed
				| _ -> ());
				PMap.iter (fun _ f ->
					try
						type_eq EqStrict (field_type f) t
					with Unify_error l ->
						error (invalid_field f.cf_name :: l)
				) an.a_fields
			with Unify_error l ->
				error (cannot_unify a b :: l))
		| TAbstract(aa,tl) when (List.exists (unify_to aa tl b) aa.a_to) ->
			()
		| _ ->
			error [cannot_unify a b])
	| TAbstract (aa,tl), _  ->
		if not (List.exists (unify_to aa tl b) aa.a_to) then error [cannot_unify a b];
	| TInst ({ cl_kind = KTypeParameter ctl } as c,pl), TAbstract (bb,tl) ->
		(* one of the constraints must satisfy the abstract *)
		if not (List.exists (fun t ->
			let t = apply_params c.cl_params pl t in
			try unify t b; true with Unify_error _ -> false
		) ctl) && not (List.exists (unify_from bb tl a b) bb.a_from) then error [cannot_unify a b];
	| _, TAbstract (bb,tl) ->
		if not (List.exists (unify_from bb tl a b) bb.a_from) then error [cannot_unify a b]
	| _ , _ ->
		error [cannot_unify a b]

and unify_abstracts a b a1 tl1 a2 tl2 =
	let f1 = unify_to a1 tl1 b in
		let f2 = unify_from a2 tl2 a b in
		if (List.exists (f1 ~allow_transitive_cast:false) a1.a_to)
		|| (List.exists (f2 ~allow_transitive_cast:false) a2.a_from)
		|| (((Meta.has Meta.CoreType a1.a_meta) || (Meta.has Meta.CoreType a2.a_meta))
			&& ((List.exists f1 a1.a_to) || (List.exists f2 a2.a_from))) then
			()
		else
			error [cannot_unify a b]

and unify_anons a b a1 a2 =
	(try
		PMap.iter (fun n f2 ->
		try
			let f1 = PMap.find n a1.a_fields in
			if not (unify_kind f1.cf_kind f2.cf_kind) then
				(match !(a1.a_status), f1.cf_kind, f2.cf_kind with
				| Opened, Var { v_read = AccNormal; v_write = AccNo }, Var { v_read = AccNormal; v_write = AccNormal } ->
					f1.cf_kind <- f2.cf_kind;
				| _ -> error [invalid_kind n f1.cf_kind f2.cf_kind]);
			if f2.cf_public && not f1.cf_public then error [invalid_visibility n];
			try
				unify_with_access (field_type f1) f2;
				(match !(a1.a_status) with
				| Statics c when not (Meta.has Meta.MaybeUsed f1.cf_meta) -> f1.cf_meta <- (Meta.MaybeUsed,[],f1.cf_pos) :: f1.cf_meta
				| _ -> ());
			with
				Unify_error l -> error (invalid_field n :: l)
		with
			Not_found ->
				match !(a1.a_status) with
				| Opened ->
					if not (link (ref None) a f2.cf_type) then error [];
					a1.a_fields <- PMap.add n f2 a1.a_fields
				| Const when Meta.has Meta.Optional f2.cf_meta ->
					()
				| _ ->
					error [has_no_field a n];
		) a2.a_fields;
		(match !(a1.a_status) with
		| Const when not (PMap.is_empty a2.a_fields) ->
			PMap.iter (fun n _ -> if not (PMap.mem n a2.a_fields) then error [has_extra_field a n]) a1.a_fields;
		| Opened ->
			a1.a_status := Closed
		| _ -> ());
		(match !(a2.a_status) with
		| Statics c -> (match !(a1.a_status) with Statics c2 when c == c2 -> () | _ -> error [])
		| EnumStatics e -> (match !(a1.a_status) with EnumStatics e2 when e == e2 -> () | _ -> error [])
		| AbstractStatics a -> (match !(a1.a_status) with AbstractStatics a2 when a == a2 -> () | _ -> error [])
		| Opened -> a2.a_status := Closed
		| Const | Extend _ | Closed -> ())
	with
		Unify_error l -> error (cannot_unify a b :: l))

and unify_from ab tl a b ?(allow_transitive_cast=true) t =
	if (List.exists (fun (a2,b2) -> fast_eq a a2 && fast_eq b b2) (!abstract_cast_stack)) then false else begin
	abstract_cast_stack := (a,b) :: !abstract_cast_stack;
	let t = apply_params ab.a_params tl t in
	let unify_func = if allow_transitive_cast then (unify ~ignoreInError:false) else type_eq EqStrict in
	let b = try
		unify_func a t;
		true
	with Unify_error _ ->
		false
	in
	abstract_cast_stack := List.tl !abstract_cast_stack;
	b
	end

and unify_to ab tl b ?(allow_transitive_cast=true) t =
	let t = apply_params ab.a_params tl t in
	let unify_func = if allow_transitive_cast then (unify ~ignoreInError:false) else type_eq EqStrict in
	try
		unify_func t b;
		true
	with Unify_error _ ->
		false

and unify_from_field ab tl a b ?(allow_transitive_cast=true) (t,cf) =
	if (List.exists (fun (a2,b2) -> fast_eq a a2 && fast_eq b b2) (!abstract_cast_stack)) then false else begin
	abstract_cast_stack := (a,b) :: !abstract_cast_stack;
	let unify_func = if allow_transitive_cast then (unify ~ignoreInError:false) else type_eq EqStrict in
	let b = try
		begin match follow cf.cf_type with
			| TFun(_,r) ->
				let monos = List.map (fun _ -> mk_mono()) cf.cf_params in
				let map t = apply_params ab.a_params tl (apply_params cf.cf_params monos t) in
				unify_func a (map t);
				List.iter2 (fun m (name,t) -> match follow t with
					| TInst ({ cl_kind = KTypeParameter constr },_) when constr <> [] ->
						List.iter (fun tc -> match follow m with TMono _ -> raise (Unify_error []) | _ -> unify m (map tc) ) constr
					| _ -> ()
				) monos cf.cf_params;
				unify_func (map r) b;
			| _ -> assert false
		end;
		true
	with Unify_error _ -> false
	in
	abstract_cast_stack := List.tl !abstract_cast_stack;
	b
	end

and unify_to_field ab tl b ?(allow_transitive_cast=true) (t,cf) =
	let a = TAbstract(ab,tl) in
	if (List.exists (fun (b2,a2) -> fast_eq a a2 && fast_eq b b2) (!abstract_cast_stack)) then false else begin
	abstract_cast_stack := (b,a) :: !abstract_cast_stack;
	let unify_func = if allow_transitive_cast then (unify ~ignoreInError:false) else type_eq EqStrict in
	let r = try
		begin match follow cf.cf_type with
			| TFun((_,_,ta) :: _,_) ->
				let monos = List.map (fun _ -> mk_mono()) cf.cf_params in
				let map t = apply_params ab.a_params tl (apply_params cf.cf_params monos t) in
				let athis = map ab.a_this in
				(* we cannot allow implicit casts when the this type is not completely known yet *)
				(* if has_mono athis then raise (Unify_error []); *)
				with_variance (type_eq EqStrict) athis (map ta);
				(* immediate constraints checking is ok here because we know there are no monomorphs *)
				List.iter2 (fun m (name,t) -> match follow t with
					| TInst ({ cl_kind = KTypeParameter constr },_) when constr <> [] ->
						List.iter (fun tc -> match follow m with TMono _ -> raise (Unify_error []) | _ -> unify m (map tc) ) constr
					| _ -> ()
				) monos cf.cf_params;
				unify_func (map t) b;
			| _ -> assert false
		end;
		true
	with Unify_error _ -> false
	in
	abstract_cast_stack := List.tl !abstract_cast_stack;
	r
	end

and unify_with_variance f t1 t2 =
	let allows_variance_to t tf = type_iseq tf t in
	match follow t1,follow t2 with
	| TInst(c1,tl1),TInst(c2,tl2) when c1 == c2 ->
		List.iter2 f tl1 tl2
	| TEnum(en1,tl1),TEnum(en2,tl2) when en1 == en2 ->
		List.iter2 f tl1 tl2
	| TAbstract(a1,tl1),TAbstract(a2,tl2) when a1 == a2 && Meta.has Meta.CoreType a1.a_meta ->
		List.iter2 f tl1 tl2
	| TAbstract(a1,pl1),TAbstract(a2,pl2) ->
		if (Meta.has Meta.CoreType a1.a_meta) && (Meta.has Meta.CoreType a2.a_meta) then begin
			let ta1 = apply_params a1.a_params pl1 a1.a_this in
			let ta2 = apply_params a2.a_params pl2 a2.a_this in
			type_eq EqStrict ta1 ta2;
		end;
		if not (List.exists (allows_variance_to t2) a1.a_to) && not (List.exists (allows_variance_to t1) a2.a_from) then
			error [cannot_unify t1 t2]
	| TAbstract(a,pl),t ->
		type_eq EqBothDynamic (apply_params a.a_params pl a.a_this) t;
		if not (List.exists (fun t2 -> allows_variance_to t (apply_params a.a_params pl t2)) a.a_to) then error [cannot_unify t1 t2]
	| t,TAbstract(a,pl) ->
		type_eq EqBothDynamic t (apply_params a.a_params pl a.a_this);
		if not (List.exists (fun t2 -> allows_variance_to t (apply_params a.a_params pl t2)) a.a_from) then error [cannot_unify t1 t2]
	| (TAnon a1 as t1), (TAnon a2 as t2) ->
		if not (List.exists (fun (a,b) -> fast_eq a t1 && fast_eq b t2) (!unify_stack)) then begin
			try
				unify_stack := (t1,t2) :: !unify_stack;
				unify_anons t1 t2 a1 a2;
				unify_stack := List.tl !unify_stack;
			with
				Unify_error l ->
					unify_stack := List.tl !unify_stack;
					error l
		end
	| _ ->
		error [cannot_unify t1 t2]

and unify_type_params a b tl1 tl2 =
	List.iter2 (fun t1 t2 ->
		try
			with_variance (type_eq EqRightDynamic) t1 t2
		with Unify_error l ->
			let err = cannot_unify a b in
			error (err :: (Invariant_parameter (t1,t2)) :: l)
	) tl1 tl2

and with_variance f t1 t2 =
	try
		f t1 t2
	with Unify_error l -> try
		unify_with_variance (with_variance f) t1 t2
	with Unify_error _ ->
		raise (Unify_error l)

and unify_with_access t1 f2 =
	match f2.cf_kind with
	(* write only *)
	| Var { v_read = AccNo } | Var { v_read = AccNever } -> unify f2.cf_type t1
	(* read only *)
	| Method MethNormal | Method MethInline | Var { v_write = AccNo } | Var { v_write = AccNever } -> unify t1 f2.cf_type
	(* read/write *)
	| _ -> with_variance (type_eq EqBothDynamic) t1 f2.cf_type

(* ======= Mapping and iterating ======= *)

let iter f e =
	match e.eexpr with
	| TConst _
	| TLocal _
	| TBreak
	| TContinue
	| TTypeExpr _ ->
		()
	| TArray (e1,e2)
	| TBinop (_,e1,e2)
	| TFor (_,e1,e2)
	| TWhile (e1,e2,_) ->
		f e1;
		f e2;
	| TThrow e
	| TField (e,_)
	| TEnumParameter (e,_,_)
	| TParenthesis e
	| TCast (e,_)
	| TUnop (_,_,e)
	| TMeta(_,e) ->
		f e
	| TArrayDecl el
	| TNew (_,_,el)
	| TBlock el ->
		List.iter f el
	| TObjectDecl fl ->
		List.iter (fun (_,e) -> f e) fl
	| TCall (e,el) ->
		f e;
		List.iter f el
	| TVar (v,eo) ->
		(match eo with None -> () | Some e -> f e)
	| TFunction fu ->
		f fu.tf_expr
	| TIf (e,e1,e2) ->
		f e;
		f e1;
		(match e2 with None -> () | Some e -> f e)
	| TSwitch (e,cases,def) ->
		f e;
		List.iter (fun (el,e2) -> List.iter f el; f e2) cases;
		(match def with None -> () | Some e -> f e)
	| TTry (e,catches) ->
		f e;
		List.iter (fun (_,e) -> f e) catches
	| TReturn eo ->
		(match eo with None -> () | Some e -> f e)

let map_expr f e =
	match e.eexpr with
	| TConst _
	| TLocal _
	| TBreak
	| TContinue
	| TTypeExpr _ ->
		e
	| TArray (e1,e2) ->
		let e1 = f e1 in
		{ e with eexpr = TArray (e1,f e2) }
	| TBinop (op,e1,e2) ->
		let e1 = f e1 in
		{ e with eexpr = TBinop (op,e1,f e2) }
	| TFor (v,e1,e2) ->
		let e1 = f e1 in
		{ e with eexpr = TFor (v,e1,f e2) }
	| TWhile (e1,e2,flag) ->
		let e1 = f e1 in
		{ e with eexpr = TWhile (e1,f e2,flag) }
	| TThrow e1 ->
		{ e with eexpr = TThrow (f e1) }
	| TEnumParameter (e1,ef,i) ->
		 { e with eexpr = TEnumParameter(f e1,ef,i) }
	| TField (e1,v) ->
		{ e with eexpr = TField (f e1,v) }
	| TParenthesis e1 ->
		{ e with eexpr = TParenthesis (f e1) }
	| TUnop (op,pre,e1) ->
		{ e with eexpr = TUnop (op,pre,f e1) }
	| TArrayDecl el ->
		{ e with eexpr = TArrayDecl (List.map f el) }
	| TNew (t,pl,el) ->
		{ e with eexpr = TNew (t,pl,List.map f el) }
	| TBlock el ->
		{ e with eexpr = TBlock (List.map f el) }
	| TObjectDecl el ->
		{ e with eexpr = TObjectDecl (List.map (fun (v,e) -> v, f e) el) }
	| TCall (e1,el) ->
		let e1 = f e1 in
		{ e with eexpr = TCall (e1, List.map f el) }
	| TVar (v,eo) ->
		{ e with eexpr = TVar (v, match eo with None -> None | Some e -> Some (f e)) }
	| TFunction fu ->
		{ e with eexpr = TFunction { fu with tf_expr = f fu.tf_expr } }
	| TIf (ec,e1,e2) ->
		let ec = f ec in
		let e1 = f e1 in
		{ e with eexpr = TIf (ec,e1,match e2 with None -> None | Some e -> Some (f e)) }
	| TSwitch (e1,cases,def) ->
		let e1 = f e1 in
		let cases = List.map (fun (el,e2) -> List.map f el, f e2) cases in
		{ e with eexpr = TSwitch (e1, cases, match def with None -> None | Some e -> Some (f e)) }
	| TTry (e1,catches) ->
		let e1 = f e1 in
		{ e with eexpr = TTry (e1, List.map (fun (v,e) -> v, f e) catches) }
	| TReturn eo ->
		{ e with eexpr = TReturn (match eo with None -> None | Some e -> Some (f e)) }
	| TCast (e1,t) ->
		{ e with eexpr = TCast (f e1,t) }
	| TMeta (m,e1) ->
		 {e with eexpr = TMeta(m,f e1)}

let map_expr_type f ft fv e =
	match e.eexpr with
	| TConst _
	| TBreak
	| TContinue
	| TTypeExpr _ ->
		{ e with etype = ft e.etype }
	| TLocal v ->
		{ e with eexpr = TLocal (fv v); etype = ft e.etype }
	| TArray (e1,e2) ->
		let e1 = f e1 in
		{ e with eexpr = TArray (e1,f e2); etype = ft e.etype }
	| TBinop (op,e1,e2) ->
		let e1 = f e1 in
		{ e with eexpr = TBinop (op,e1,f e2); etype = ft e.etype }
	| TFor (v,e1,e2) ->
		let v = fv v in
		let e1 = f e1 in
		{ e with eexpr = TFor (v,e1,f e2); etype = ft e.etype }
	| TWhile (e1,e2,flag) ->
		let e1 = f e1 in
		{ e with eexpr = TWhile (e1,f e2,flag); etype = ft e.etype }
	| TThrow e1 ->
		{ e with eexpr = TThrow (f e1); etype = ft e.etype }
	| TEnumParameter (e1,ef,i) ->
		{ e with eexpr = TEnumParameter(f e1,ef,i); etype = ft e.etype }
	| TField (e1,v) ->
		let e1 = f e1 in
		let v = try
			let n = match v with
				| FClosure _ -> raise Not_found
				| FAnon f | FInstance (_,_,f) | FStatic (_,f) -> f.cf_name
				| FEnum (_,f) -> f.ef_name
				| FDynamic n -> n
			in
			quick_field e1.etype n
		with Not_found ->
			v
		in
		{ e with eexpr = TField (e1,v); etype = ft e.etype }
	| TParenthesis e1 ->
		{ e with eexpr = TParenthesis (f e1); etype = ft e.etype }
	| TUnop (op,pre,e1) ->
		{ e with eexpr = TUnop (op,pre,f e1); etype = ft e.etype }
	| TArrayDecl el ->
		{ e with eexpr = TArrayDecl (List.map f el); etype = ft e.etype }
	| TNew (c,pl,el) ->
		let et = ft e.etype in
		(* make sure that we use the class corresponding to the replaced type *)
		let t = match c.cl_kind with
			| KTypeParameter _ | KGeneric ->
				et
			| _ ->
				ft (TInst(c,pl))
		in
		let c, pl = (match follow t with TInst (c,pl) -> (c,pl) | TAbstract({a_impl = Some c},pl) -> c,pl | t -> error [has_no_field t "new"]) in
		{ e with eexpr = TNew (c,pl,List.map f el); etype = et }
	| TBlock el ->
		{ e with eexpr = TBlock (List.map f el); etype = ft e.etype }
	| TObjectDecl el ->
		{ e with eexpr = TObjectDecl (List.map (fun (v,e) -> v, f e) el); etype = ft e.etype }
	| TCall (e1,el) ->
		let e1 = f e1 in
		{ e with eexpr = TCall (e1, List.map f el); etype = ft e.etype }
	| TVar (v,eo) ->
		{ e with eexpr = TVar (fv v, match eo with None -> None | Some e -> Some (f e)); etype = ft e.etype }
	| TFunction fu ->
		let fu = {
			tf_expr = f fu.tf_expr;
			tf_args = List.map (fun (v,o) -> fv v, o) fu.tf_args;
			tf_type = ft fu.tf_type;
		} in
		{ e with eexpr = TFunction fu; etype = ft e.etype }
	| TIf (ec,e1,e2) ->
		let ec = f ec in
		let e1 = f e1 in
		{ e with eexpr = TIf (ec,e1,match e2 with None -> None | Some e -> Some (f e)); etype = ft e.etype }
	| TSwitch (e1,cases,def) ->
		let e1 = f e1 in
		let cases = List.map (fun (el,e2) -> List.map f el, f e2) cases in
		{ e with eexpr = TSwitch (e1, cases, match def with None -> None | Some e -> Some (f e)); etype = ft e.etype }
	| TTry (e1,catches) ->
		let e1 = f e1 in
		{ e with eexpr = TTry (e1, List.map (fun (v,e) -> fv v, f e) catches); etype = ft e.etype }
	| TReturn eo ->
		{ e with eexpr = TReturn (match eo with None -> None | Some e -> Some (f e)); etype = ft e.etype }
	| TCast (e1,t) ->
		{ e with eexpr = TCast (f e1,t); etype = ft e.etype }
	| TMeta (m,e1) ->
		{e with eexpr = TMeta(m, f e1); etype = ft e.etype }

let resolve_typedef t =
	match t with
	| TClassDecl _ | TEnumDecl _ | TAbstractDecl _ -> t
	| TTypeDecl td ->
		match follow td.t_type with
		| TEnum (e,_) -> TEnumDecl e
		| TInst (c,_) -> TClassDecl c
		| TAbstract (a,_) -> TAbstractDecl a
		| _ -> t

module TExprToExpr = struct
	let tpath p mp pl =
		if snd mp = snd p then
			CTPath {
				tpackage = fst p;
				tname = snd p;
				tparams = List.map (fun t -> TPType t) pl;
				tsub = None;
			}
		else CTPath {
				tpackage = fst mp;
				tname = snd mp;
				tparams = List.map (fun t -> TPType t) pl;
				tsub = Some (snd p);
			}

	let rec convert_type = function
		| TMono r ->
			(match !r with
			| None -> raise Exit
			| Some t -> convert_type t)
		| TInst ({cl_private = true; cl_path=_,name},tl)
		| TEnum ({e_private = true; e_path=_,name},tl)
		| TType ({t_private = true; t_path=_,name},tl)
		| TAbstract ({a_private = true; a_path=_,name},tl) ->
			CTPath {
				tpackage = [];
				tname = name;
				tparams = List.map (fun t -> TPType (convert_type' t)) tl;
				tsub = None;
			}
		| TEnum (e,pl) ->
			tpath e.e_path e.e_module.m_path (List.map convert_type' pl)
		| TInst({cl_kind = KTypeParameter _} as c,pl) ->
			tpath ([],snd c.cl_path) ([],snd c.cl_path) (List.map convert_type' pl)
		| TInst (c,pl) ->
			tpath c.cl_path c.cl_module.m_path (List.map convert_type' pl)
		| TType (t,pl) as tf ->
			(* recurse on type-type *)
			if (snd t.t_path).[0] = '#' then convert_type (follow tf) else tpath t.t_path t.t_module.m_path (List.map convert_type' pl)
		| TAbstract (a,pl) ->
			tpath a.a_path a.a_module.m_path (List.map convert_type' pl)
		| TFun (args,ret) ->
			CTFunction (List.map (fun (_,_,t) -> convert_type' t) args, (convert_type' ret))
		| TAnon a ->
			begin match !(a.a_status) with
			| Statics c -> tpath ([],"Class") ([],"Class") [tpath c.cl_path c.cl_path [],null_pos]
			| EnumStatics e -> tpath ([],"Enum") ([],"Enum") [tpath e.e_path e.e_path [],null_pos]
			| _ ->
				CTAnonymous (PMap.foldi (fun _ f acc ->
					{
						cff_name = f.cf_name,null_pos;
						cff_kind = FVar (mk_type_hint f.cf_type null_pos,None);
						cff_pos = f.cf_pos;
						cff_doc = f.cf_doc;
						cff_meta = f.cf_meta;
						cff_access = [];
					} :: acc
				) a.a_fields [])
			end
		| (TDynamic t2) as t ->
			tpath ([],"Dynamic") ([],"Dynamic") (if t == t_dynamic then [] else [convert_type' t2])
		| TLazy f ->
			convert_type ((!f)())

	and convert_type' t =
		convert_type t,null_pos

	and mk_type_hint t p =
		match follow t with
		| TMono _ -> None
		| _ -> (try Some (convert_type t,p) with Exit -> None)

	let rec convert_expr e =
		let full_type_path t =
			let mp,p = match t with
			| TClassDecl c -> c.cl_module.m_path,c.cl_path
			| TEnumDecl en -> en.e_module.m_path,en.e_path
			| TAbstractDecl a -> a.a_module.m_path,a.a_path
			| TTypeDecl t -> t.t_module.m_path,t.t_path
			in
			if snd mp = snd p then p else (fst mp) @ [snd mp],snd p
		in
		let mk_path = expr_of_type_path in
		let mk_ident = function
			| "`trace" -> Ident "trace"
			| n -> Ident n
		in
		let eopt = function None -> None | Some e -> Some (convert_expr e) in
		((match e.eexpr with
		| TConst c ->
			EConst (tconst_to_const c)
		| TLocal v -> EConst (mk_ident v.v_name)
		| TArray (e1,e2) -> EArray (convert_expr e1,convert_expr e2)
		| TBinop (op,e1,e2) -> EBinop (op, convert_expr e1, convert_expr e2)
		| TField (e,f) -> EField (convert_expr e, field_name f)
		| TTypeExpr t -> fst (mk_path (full_type_path t) e.epos)
		| TParenthesis e -> EParenthesis (convert_expr e)
		| TObjectDecl fl -> EObjectDecl (List.map (fun (f,e) -> (f,null_pos), convert_expr e) fl)
		| TArrayDecl el -> EArrayDecl (List.map convert_expr el)
		| TCall (e,el) -> ECall (convert_expr e,List.map convert_expr el)
		| TNew (c,pl,el) -> ENew ((match (try convert_type (TInst (c,pl)) with Exit -> convert_type (TInst (c,[]))) with CTPath p -> p,null_pos | _ -> assert false),List.map convert_expr el)
		| TUnop (op,p,e) -> EUnop (op,p,convert_expr e)
		| TFunction f ->
			let arg (v,c) = (v.v_name,v.v_pos), false, v.v_meta, mk_type_hint v.v_type null_pos, (match c with None -> None | Some c -> Some (EConst (tconst_to_const c),e.epos)) in
			EFunction (None,{ f_params = []; f_args = List.map arg f.tf_args; f_type = mk_type_hint f.tf_type null_pos; f_expr = Some (convert_expr f.tf_expr) })
		| TVar (v,eo) ->
			EVars ([(v.v_name,v.v_pos), mk_type_hint v.v_type v.v_pos, eopt eo])
		| TBlock el -> EBlock (List.map convert_expr el)
		| TFor (v,it,e) ->
			let ein = (EIn ((EConst (Ident v.v_name),it.epos),convert_expr it),it.epos) in
			EFor (ein,convert_expr e)
		| TIf (e,e1,e2) -> EIf (convert_expr e,convert_expr e1,eopt e2)
		| TWhile (e1,e2,flag) -> EWhile (convert_expr e1, convert_expr e2, flag)
		| TSwitch (e,cases,def) ->
			let cases = List.map (fun (vl,e) ->
				List.map convert_expr vl,None,(match e.eexpr with TBlock [] -> None | _ -> Some (convert_expr e)),e.epos
			) cases in
			let def = match eopt def with None -> None | Some (EBlock [],_) -> Some (None,null_pos) | Some e -> Some (Some e,pos e) in
			ESwitch (convert_expr e,cases,def)
		| TEnumParameter _ ->
			(* these are considered complex, so the AST is handled in TMeta(Meta.Ast) *)
			assert false
		| TTry (e,catches) ->
			let e1 = convert_expr e in
			let catches = List.map (fun (v,e) ->
				let ct = try convert_type v.v_type,null_pos with Exit -> assert false in
				let e = convert_expr e in
				(v.v_name,v.v_pos),ct,e,(pos e)
			) catches in
			ETry (e1,catches)
		| TReturn e -> EReturn (eopt e)
		| TBreak -> EBreak
		| TContinue -> EContinue
		| TThrow e -> EThrow (convert_expr e)
		| TCast (e,t) ->
			let t = (match t with
				| None -> None
				| Some t ->
					let t = (match t with TClassDecl c -> TInst (c,[]) | TEnumDecl e -> TEnum (e,[]) | TTypeDecl t -> TType (t,[]) | TAbstractDecl a -> TAbstract (a,[])) in
					Some (try convert_type t,null_pos with Exit -> assert false)
			) in
			ECast (convert_expr e,t)
		| TMeta ((Meta.Ast,[e1,_],_),_) -> e1
		| TMeta (m,e) -> EMeta(m,convert_expr e))
		,e.epos)

end

module Texpr = struct
	let equal_fa fa1 fa2 = match fa1,fa2 with
		| FStatic(c1,cf1),FStatic(c2,cf2) -> c1 == c2 && cf1 == cf2
		| FInstance(c1,tl1,cf1),FInstance(c2,tl2,cf2) -> c1 == c2 && safe_for_all2 type_iseq tl1 tl2 && cf1 == cf2
		(* TODO: This is technically not correct but unfortunately the compiler makes a distinct tclass_field for each anon field access. *)
		| FAnon cf1,FAnon cf2 -> cf1.cf_name = cf2.cf_name
		| FDynamic s1,FDynamic s2 -> s1 = s2
		| FClosure(None,cf1),FClosure(None,cf2) -> cf1 == cf2
		| FClosure(Some(c1,tl1),cf1),FClosure(Some(c2,tl2),cf2) -> c1 == c2 && safe_for_all2 type_iseq tl1 tl2 && cf1 == cf2
		| FEnum(en1,ef1),FEnum(en2,ef2) -> en1 == en2 && ef1 == ef2
		| _ -> false

	let rec equal e1 e2 = match e1.eexpr,e2.eexpr with
		| TConst ct1,TConst ct2 -> ct1 = ct2
		| TLocal v1,TLocal v2 -> v1 == v2
		| TArray(eb1,ei1),TArray(eb2,ei2) -> equal eb1 eb2 && equal ei1 ei2
		| TBinop(op1,lhs1,rhs1),TBinop(op2,lhs2,rhs2) -> op1 = op2 && equal lhs1 lhs2 && equal rhs1 rhs2
		| TField(e1,fa1),TField(e2,fa2) -> equal e1 e2 && equal_fa fa1 fa2
		| TTypeExpr mt1,TTypeExpr mt2 -> mt1 == mt2
		| TParenthesis e1,TParenthesis e2 -> equal e1 e2
		| TObjectDecl fl1,TObjectDecl fl2 -> safe_for_all2 (fun (s1,e1) (s2,e2) -> s1 = s2 && equal e1 e2) fl1 fl2
		| (TArrayDecl el1,TArrayDecl el2) | (TBlock el1,TBlock el2) -> safe_for_all2 equal el1 el2
		| TCall(e1,el1),TCall(e2,el2) -> equal e1 e2 && safe_for_all2 equal el1 el2
		| TNew(c1,tl1,el1),TNew(c2,tl2,el2) -> c1 == c2 && safe_for_all2 type_iseq tl1 tl2 && safe_for_all2 equal el1 el2
		| TUnop(op1,flag1,e1),TUnop(op2,flag2,e2) -> op1 = op2 && flag1 = flag2 && equal e1 e2
		| TFunction tf1,TFunction tf2 -> tf1 == tf2
		| TVar(v1,None),TVar(v2,None) -> v1 == v2
		| TVar(v1,Some e1),TVar(v2,Some e2) -> v1 == v2 && equal e1 e2
		| TFor(v1,ec1,eb1),TFor(v2,ec2,eb2) -> v1 == v2 && equal ec1 ec2 && equal eb1 eb2
		| TIf(e1,ethen1,None),TIf(e2,ethen2,None) -> equal e1 e2 && equal ethen1 ethen2
		| TIf(e1,ethen1,Some eelse1),TIf(e2,ethen2,Some eelse2) -> equal e1 e2 && equal ethen1 ethen2 && equal eelse1 eelse2
		| TWhile(e1,eb1,flag1),TWhile(e2,eb2,flag2) -> equal e1 e2 && equal eb2 eb2 && flag1 = flag2
		| TSwitch(e1,cases1,eo1),TSwitch(e2,cases2,eo2) ->
			equal e1 e2 &&
			safe_for_all2 (fun (el1,e1) (el2,e2) -> safe_for_all2 equal el1 el2 && equal e1 e2) cases1 cases2 &&
			(match eo1,eo2 with None,None -> true | Some e1,Some e2 -> equal e1 e2 | _ -> false)
		| TTry(e1,catches1),TTry(e2,catches2) -> equal e1 e2 && safe_for_all2 (fun (v1,e1) (v2,e2) -> v1 == v2 && equal e1 e2) catches1 catches2
		| TReturn None,TReturn None -> true
		| TReturn(Some e1),TReturn(Some e2) -> equal e1 e2
		| TThrow e1,TThrow e2 -> equal e1 e2
		| TCast(e1,None),TCast(e2,None) -> equal e1 e2
		| TCast(e1,Some mt1),TCast(e2,Some mt2) -> equal e1 e2 && mt1 == mt2
		| TMeta((m1,el1,_),e1),TMeta((m2,el2,_),e2) -> m1 = m2 && safe_for_all2 (fun e1 e2 -> (* TODO: cheating? *) (Ast.s_expr e1) = (Ast.s_expr e2)) el1 el2 && equal e1 e2
		| (TBreak,TBreak) | (TContinue,TContinue) -> true
		| TEnumParameter(e1,ef1,i1),TEnumParameter(e2,ef2,i2) -> equal e1 e2 && ef1 == ef2 && i1 = i2
		| _ -> false

	let duplicate_tvars e =
		let vars = Hashtbl.create 0 in
		let copy_var v =
			let v2 = alloc_var v.v_name v.v_type v.v_pos in
			v2.v_meta <- v.v_meta;
			Hashtbl.add vars v.v_id v2;
			v2;
		in
		let rec build_expr e =
			match e.eexpr with
			| TVar (v,eo) ->
				let v2 = copy_var v in
				{e with eexpr = TVar(v2, Option.map build_expr eo)}
			| TFor (v,e1,e2) ->
				let v2 = copy_var v in
				{e with eexpr = TFor(v2, build_expr e1, build_expr e2)}
			| TTry (e1,cl) ->
				let cl = List.map (fun (v,e) ->
					let v2 = copy_var v in
					v2, build_expr e
				) cl in
				{e with eexpr = TTry(build_expr e1, cl)}
			| TFunction f ->
				let args = List.map (fun (v,c) -> copy_var v, c) f.tf_args in
				let f = {
					tf_args = args;
					tf_type = f.tf_type;
					tf_expr = build_expr f.tf_expr;
				} in
				{e with eexpr = TFunction f}
			| TLocal v ->
				(try
					let v2 = Hashtbl.find vars v.v_id in
					{e with eexpr = TLocal v2}
				with _ ->
					e)
			| _ ->
				map_expr build_expr e
		in
		build_expr e

	let rec skip e = match e.eexpr with
		| TParenthesis e1 | TMeta(_,e1) | TBlock [e1] | TCast(e1,None) -> skip e1
		| _ -> e

	let foldmap_list f acc el =
		let rec loop acc el acc2 = (match el with
			| [] -> acc,(List.rev acc2)
			| e1 :: el ->
				let acc,e1 = f acc e1 in
				loop acc el (e1 :: acc2))
		in loop acc el []

	let foldmap_opt f acc eo = match eo with
		| Some(e) -> let acc,e = f acc e in acc,Some(e)
		| None    -> acc,eo

	let foldmap_pairs f acc pairs =
		let acc,pairs = List.fold_left
			(fun (acc,el) (v,e) -> let acc,e = f acc e in (acc,(v,e) :: el))
			(acc,[])
			pairs
		in acc,(List.rev pairs)

	let foldmap f acc e =
		begin match e.eexpr with
		| TConst _
		| TLocal _
		| TBreak
		| TContinue
		| TTypeExpr _ ->
			acc,e
		| TArray (e1,e2) ->
			let acc,e1 = f acc e1 in
			let acc,e2 = f acc e2 in
			acc,{ e with eexpr = TArray (e1, e2) }
		| TBinop (op,e1,e2) ->
			let acc,e1 = f acc e1 in
			let acc,e2 = f acc e2 in
			acc,{ e with eexpr = TBinop (op,e1,e2) }
		| TFor (v,e1,e2) ->
			let acc,e1 = f acc e1 in
			let acc,e2 = f acc e2 in
			acc,{ e with eexpr = TFor (v,e1,e2) }
		| TWhile (e1,e2,flag) ->
			let acc,e1 = f acc e1 in
			let acc,e2 = f acc e2 in
			acc,{ e with eexpr = TWhile (e1,e2,flag) }
		| TThrow e1 ->
			let acc,e1 = f acc e1 in
			acc,{ e with eexpr = TThrow (e1) }
		| TEnumParameter (e1,ef,i) ->
			let acc,e1 = f acc e1 in
			acc,{ e with eexpr = TEnumParameter(e1,ef,i) }
		| TField (e1,v) ->
			let acc,e1 = f acc e1 in
			acc,{ e with eexpr = TField (e1,v) }
		| TParenthesis e1 ->
			let acc,e1 = f acc e1 in
			acc,{ e with eexpr = TParenthesis (e1) }
		| TUnop (op,pre,e1) ->
			let acc,e1 = f acc e1 in
			acc,{ e with eexpr = TUnop (op,pre,e1) }
		| TArrayDecl el ->
			let acc,el = foldmap_list f acc el in
			acc,{ e with eexpr = TArrayDecl el }
		| TNew (t,pl,el) ->
			let acc,el = foldmap_list f acc el in
			acc,{ e with eexpr = TNew (t,pl,el) }
		| TBlock el ->
			let acc,el = foldmap_list f acc el in
			acc,{ e with eexpr = TBlock (el) }
		| TObjectDecl el ->
			let acc,el = foldmap_pairs f acc el in
			acc,{ e with eexpr = TObjectDecl el }
		| TCall (e1,el) ->
			let acc,e1 = f acc e1 in
			let acc,el = foldmap_list f acc el in
			acc,{ e with eexpr = TCall (e1,el) }
		| TVar (v,eo) ->
			let acc,eo = foldmap_opt f acc eo in
			acc,{ e with eexpr = TVar (v, eo) }
		| TFunction fu ->
			let acc,e1 = f acc fu.tf_expr in
			acc,{ e with eexpr = TFunction { fu with tf_expr = e1 } }
		| TIf (ec,e1,eo) ->
			let acc,ec = f acc ec in
			let acc,e1 = f acc e1 in
			let acc,eo = foldmap_opt f acc eo in
			acc,{ e with eexpr = TIf (ec,e1,eo)}
		| TSwitch (e1,cases,def) ->
			let acc,e1 = f acc e1 in
			let acc,cases = List.fold_left (fun (acc,cases) (el,e2) ->
				let acc,el = foldmap_list f acc el in
				let acc,e2 = f acc e2 in
				acc,((el,e2) :: cases)
			) (acc,[]) cases in
			let acc,def = foldmap_opt f acc def in
			acc,{ e with eexpr = TSwitch (e1, cases, def) }
		| TTry (e1,catches) ->
			let acc,e1 = f acc e1 in
			let acc,catches = foldmap_pairs f acc catches in
			acc,{ e with eexpr = TTry (e1, catches) }
		| TReturn eo ->
			let acc,eo = foldmap_opt f acc eo in
			acc,{ e with eexpr = TReturn eo }
		| TCast (e1,t) ->
			let acc,e1 = f acc e1 in
			acc,{ e with eexpr = TCast (e1,t) }
		| TMeta (m,e1) ->
			let acc,e1 = f acc e1 in
			acc,{ e with eexpr = TMeta(m,e1)}
		end
end

module ExtType = struct
	let is_void = function
		| TAbstract({a_path=[],"Void"},_) -> true
		| _ -> false
end




