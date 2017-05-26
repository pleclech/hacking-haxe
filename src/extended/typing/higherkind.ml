open Utils
open Ast
open Typedef
open Typeutility
open Onthefly

let debug_expr_with_type e =
	let s_type = Typeutility.s_type (print_context()) in
	let es = Typeutility.s_expr_pretty false "    " false s_type e in
	let t = s_type_kind e.etype in
	Printf.printf "%s : %s\n%!" es t;
	e

let rec follow_no_ttype t = match t with
	| TMono r ->
		(match !r with
		| Some t -> follow_no_ttype t
		| _ -> t)
	| TLazy f ->
		follow_no_ttype (!f())
	| _ -> t

module In = struct
    let name = "In"
    let meta_name = ":"^name
    let meta = Meta.Custom meta_name
	let id = ref 0 
    
    let mk_name arity = if arity <= 0 then name else Printf.sprintf "%s%d" name arity
	
	let t_ref:(tdef option) ref = ref None
	let t2_ref:(tabstract option) ref = ref None

	let mk_ct1 p = CTPath {tpackage=[];tname=(mk_name 1);tparams=[TPType(CTOptional None, p)];tsub=None;}, p

	let mk_t tl =
		incr id;
		let mk_path l (p,n) =
			let n = mk_name l in
			(*let n = Printf.sprintf "%s_%d" n !id in*)
			p, n
		in 
		let l = List.length tl in
		match List.length tl with
		(*| 0 -> (match !t_ref with Some def -> TType(def , tl) | None -> raise Not_found)*)
		| 1 -> (match !t2_ref with Some a -> TAbstract({a with a_path=mk_path l a.a_path}, tl) | None -> raise Not_found)
		| _ -> raise Not_found

	let retype_expr e =
		match follow e.etype with
		| TAbstract(a, [t]) when Meta.has meta a.a_meta -> {e with etype=t}
		| _ -> e
	
end 

module InList = struct
    let name = "InList"
    let meta_name = ":"^name
    let meta = Meta.Custom meta_name

	let mk_name arity = if arity <= 0 then name else Printf.sprintf "%s%d" name arity

	let t_ref:(tabstract option) ref = ref None
	let t2_ref:(tabstract option) ref = ref None

	let mk_t tl =		
		let mk_path l (p,n) =
			let n = mk_name l in
			p, n
		in 
		let l = List.length tl in
		if l < 0 then raise Not_found
		else if l=0 then (match !t_ref with Some a -> TAbstract(a, tl) | None -> raise Not_found) 
		else (match !t2_ref with Some a -> TAbstract({a with a_path=mk_path l a.a_path}, tl) | None -> raise Not_found)
end

let name = "HigherKind"
let meta_name = ":"^name
let meta = Meta.Custom meta_name

let mk_name arity = Printf.sprintf "%s%d" name arity

let mk_s tname name arity =
    if arity <= 0 then raise Not_found
    else
        Printf.sprintf "@%s @:forward abstract %s<C,I,%s>(C) to C {}" meta_name tname (mk_sarg "T" arity)

let mk_from_tparam t p =
	let params = t.tparams in
	match List.length params with
	| 0 -> raise Not_found
	| _ as l ->
		let tname = Printf.sprintf "%s%d" name l in
		let tc = TPType(CTPath {tpackage=[];tname=t.tname;tparams=[];tsub=None;}, p) in
		let th = TPType(In.mk_ct1 p) in
		let tparams = tc::th::t.tparams in
		let t = {tpackage=[]; tsub=None; tname; tparams} in
		(t,p)

let t_ref:(tabstract option) ref = ref None
let t2_ref:(tabstract option) ref = ref None
let any_t_ref:(tabstract option) ref = ref None

let is_hkt m = Meta.has meta m
let is_in m = Meta.has In.meta m
let is_inlist m = Meta.has InList.meta m
let is_in_t t = match follow t with TAbstract(a, _) when is_in a.a_meta -> true | _ -> false

let mk_with_abstract2 a ap t =
	let l = List.length a.a_params - 2 in
	if l <= 0 then raise Not_found
	else
		let mk_in tl =
			let rec loop xs lin lout lins l = 
				match xs, l with
				| x::xs, _ ->
					(*let x = follow x in*)
					let t = TMono( ref (Some x) ) in
					let lin = (In.mk_t [ t ])::lin in
					let lout = (In.mk_t [ x ])::lout in
					let lins = t::lins in
					if l=1 then (List.rev xs)@lin, lout, lins
					else loop xs lin lout lins (l-1)
				| _ -> raise Not_found
			in loop (List.rev tl) [] [] [] l
		in
		match t with
		| TInst(def, tl) ->
			let lin, lout, lins = mk_in tl in
			let lins = In.mk_t [ TMono(ref (Some(InList.mk_t lins))) ] in
			(TAbstract(a, TInst(def, lin)::lins::lout))
		| TAbstract(def, tl) ->
			let lin, lout, lins = mk_in tl in
			let lins = In.mk_t [ TMono(ref (Some(InList.mk_t lins))) ] in
			(TAbstract(a, TAbstract(def, lin)::lins::lout))
		| TEnum(def, tl) ->
			let lin, lout, lins = mk_in tl in
			let lins = In.mk_t [ TMono(ref (Some(InList.mk_t lins))) ] in
			(TAbstract(a, TEnum(def, lin)::lins::lout))
		| TType(def, tl) ->
			let lin, lout, lins = mk_in tl in
			let lins = In.mk_t [ TMono(ref (Some(InList.mk_t lins))) ] in
			(TAbstract(a, TType(def, lin)::lins::lout))		
		| _ -> raise Not_found

let apply_in inlist tl =
	let rec loop xs ys = match xs,ys with
	| x::xs, y::ys ->
		(match x with
		| TMono r ->
			let y = (match (follow y) with TAbstract(def, [x]) when is_in def.a_meta -> x | _ -> y) in
			r := Some y;
			loop xs ys
		| _ -> loop xs ys
		)
	| _ -> ()
	in loop (List.rev inlist) (List.rev tl)

let erase_in inlist =
	let rec loop xs = match xs with
	| x::xs ->
		(match x with
		| TMono r ->
			begin match !r with
			| Some t ->
				(match !any_t_ref with None -> () | Some a -> r := Some (TAbstract(a, [])))
			| _ -> ()
			end;
			loop xs
		| _ -> loop xs
		)
	| _ -> ()
	in loop inlist

let rec fill_in_list tl = match tl with
	| c::TAbstract(def,[TMono r])::tl when is_in def.a_meta ->
			let ins = ref [] in
			let rec loop t =
				let t' = follow_no_ttype t in
				match t' with
				| TAbstract(def, [t]) when is_in def.a_meta -> ins := t::!ins
				| TAbstract(def, tl) when is_hkt def.a_meta ->
					let tl' = fill_in_list tl in
					apply_in tl' tl
				| TInst(_, tl) | TAbstract(_, tl) | TEnum(_, tl) | TType(_, tl) -> List.iter (fun t -> loop t) tl
				| TFun (tl,r) ->
					List.iter (fun (s,o,t) -> loop t) tl;
					loop r
				| _ -> () 
			in loop c;
			r := Some (InList.mk_t (List.rev !ins));
			!ins
	| _ -> []

let apply_with_abstract a tl =
	if not (is_hkt a.a_meta) then raise Not_found
	else
	match tl with
		| c::TAbstract(def,[(TMono r) as t])::tl' when is_in def.a_meta ->
			begin match follow t with
			| TAbstract(def, ins) when is_inlist def.a_meta ->
				apply_in ins tl';
				c,ins,tl'
			| _ -> assert false
			end
		| _ ->
			assert false

let fill_with_abstract a tl =
	ignore(fill_in_list tl);
	apply_with_abstract a tl

let get_impl_from_abstract aa tl =
	if not (is_hkt aa.a_meta) then raise Not_found
	else
		let c,_,tla = fill_with_abstract aa tl in
		let l = List.length tla in
		match c with
			| TInst ({cl_kind = KTypeParameter tl}, _) -> raise Not_found
			| TInst(i,tl) when l=(List.length tl) -> TInst(i,tla)
			| TEnum(e,tl) when l=(List.length tl) -> TEnum(e,tla)
			| TAbstract(a,tl) when l=(List.length tl) -> TAbstract(a,tla)
			| TType(t,tl) when l=(List.length tl) -> TType(t, tla)
			| _ as t -> t

let get_impl_from_type t = match follow t with
	| TAbstract (aa,tl) -> (try get_impl_from_abstract aa tl with Not_found -> t)
	| _ -> t

let rec erase_type t with_type =
	let rec loop t1 t2 = match get_impl_from_type t1, get_impl_from_type t2 with
	| TInst(i1,tl1), TInst(i2,tl2) ->
		let tl1 = if tl2=[] then tl2
		else begin
			let acc = ref [] in
			List.iter2 (fun t1 t2 -> acc := (loop t1 t2) :: !acc) tl1 tl2;
			List.rev !acc
		end
		in
		TInst(i1, tl1)
	| TEnum(e1,tl1), TEnum(e2,tl2) ->
		let tl1 = if tl2=[] then tl2
		else begin
			let acc = ref [] in
			List.iter2 (fun t1 t2 -> acc := (loop t1 t2) :: !acc) tl1 tl2;
			List.rev !acc
		end
		in
		TEnum(e1,tl1)
	| TType(e1,tl1), TType(e2,tl2) ->
		let tl1 = if tl2=[] then tl2
		else begin
			let acc = ref [] in
			List.iter2 (fun t1 t2 -> acc := (loop t1 t2) :: !acc) tl1 tl2;
			List.rev !acc
		end
		in
		TType(e1,tl1)
	| TAbstract(a1,tl1), TAbstract(a2,tl2) ->
		let tl1 = if tl2=[] then tl2
		else begin
			let acc = ref [] in
			List.iter2 (fun t1 t2 -> acc := (loop t1 t2) :: !acc) tl1 tl2;
			List.rev !acc
		end
		in
		TAbstract(a1,tl1)
	| _ -> t
	in 
	loop t with_type

let erase_type_for_class_field cf = match cf.cf_override with
	| Some cf2 ->
		(match cf2.cf_type,cf.cf_type with
		| TFun(args2, ret2), TFun(args1, ret1) ->
			let args = ref [] in
			List.iter2 ( fun (s,o,t1) (_,_,t2) ->
				args := (s,o,(erase_type t1 t2)) :: !args
			) args1 args2;
			let ret = erase_type ret1 ret2 in
			cf.cf_type <- TFun(List.rev !args, ret)
		| _ -> ()
		)
	| None -> ()

let get_type t = try get_impl_from_type t with Not_found -> t

let retype_expr e = In.retype_expr (try let t = get_impl_from_type e.etype in {e with etype=t} with Not_found -> e)

;;

register_factory name mk_s;
