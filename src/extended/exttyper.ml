open Ast
open Globals
open Meta
open Type
open Error

let prepare_using_field_ref:(tclass_field -> tclass_field) ref = ref (fun _ -> assert false)
let set_return_partial_type_ref:(bool -> unit) ref = ref (fun _ -> assert false)

module AbstractGraph = struct
	type tp = t

	let rec partial_eq a b =
			if a == b then
				true
			else match a , b with
			| TFun (l1,r1) , TFun (l2,r2) when List.length l1 = List.length l2 ->
				List.for_all2 (fun (_,_,t1) (_,_,t2) -> partial_eq t1 t2) l1 l2 && partial_eq r1 r2
			| TType (t1,l1), TType (t2,l2) ->
				t1 == t2 && List.for_all2 partial_eq l1 l2
			| TEnum (e1,l1), TEnum (e2,l2) ->
				e1 == e2 && List.for_all2 partial_eq l1 l2
			| TInst (c1,l1), TInst (c2,l2) ->
				c1 == c2 && List.for_all2 partial_eq l1 l2
			| TAbstract (a1,l1), TAbstract (a2,l2) ->
				a1 == a2
			| _ , _ ->
				false

	type graph_t = abstract_graph_t

	let succs t g = List.find (fun (a, _) -> partial_eq t a) g.edges
	let preds t g = List.find (fun (a, _) -> partial_eq t a) g.preds

	let empty_pl t = match t with
		| TAbstract(a,x::xs) -> TAbstract(a, [])
		| _ -> t

	let build tdecls =
		let t = Common.timer ["AbstractTransitive";"graph build"] in
		let visited_ref = ref [] in
		let visited t = if List.exists (fast_eq t) !visited_ref then true else (visited_ref := t::!visited_ref; false)  in

		let edges_ref = ref [] in
		let preds_ref = ref [] in

		let find_default t items = 
			try List.find (fun (a, _) -> partial_eq a t) !items 
			with Not_found ->
				let item = (t, ref []) in
				items := item::!items;
				item
		in

		let add_pred f t =
			let _, preds = (find_default f preds_ref) in
			preds := (t)::!preds
		in
		let add tdecl =
				match tdecl with
				| TAbstractDecl a ->
					let ap = List.map snd a.a_params in
					let t = TAbstract(a, ap) in
					if not (visited t) then
						let _, edges = find_default t edges_ref in
						List.iter (fun ((_,cf) as tcf) ->
								match follow cf.cf_type with
								| TFun(_, r) ->
									let r = follow r in
									add_pred r t; 
									edges := (ToField((a, ap), tcf, r))::!edges
								| _ -> ()
						)  a.a_to_field;

						List.iter (fun r ->
							let r = follow r in
							add_pred r t; 
							edges := (To((a, ap), t, r))::!edges
						)  a.a_to;

						List.iter (fun ((_, cf) as tcf) ->
							match follow cf.cf_type with
								| TFun((_,_,ta) :: _, r) ->
									let r = follow r in
									let ta = follow ta in
									let _, edges = find_default ta edges_ref in
									edges := (FromField((a, ap), tcf, r))::!edges;
									add_pred r ta
								| _ -> ()
						) a.a_from_field;

						List.iter (fun r ->
							let r = follow r in
							let _, edges = find_default r edges_ref in
							edges := (From((a, ap), r, t))::!edges;
							add_pred t r
						) a.a_from
						
				| _ -> ()
		in
		List.iter add tdecls;
		t();
		{
			edges = !edges_ref;
			preds = !preds_ref;
		} 

	let to_dot g = 
		let open Printf in
		let edge_to_s a b = 
			let a = empty_pl a in
			let b = empty_pl b in
			sprintf "\"%s\" -> \"%s\"" (s_type_kind a) (s_type_kind b) in
		let s = List.fold_left (fun acc (k, lst)  ->
			sprintf "%s%s" acc (
				List.fold_left (fun acc edge ->
					match edge with
					| ToField(_, _, r) | To(_, _, r) -> sprintf "%s\n%s [color=green];" acc (edge_to_s k r)
					| FromField(_, _, r) | From(_, _, r) -> sprintf "%s\n%s [color=blue,style=dotted];" acc (edge_to_s k r)
				) "" !lst
			)
		) "" g.edges
		in sprintf "digraph abstract {%s\n}\n" s

	let register_module m =
		let og_ref = ref None in
		let mtypes_ref = ref [] in
		let build_fn() = match !og_ref with
			| Some g -> g
			| None -> 
				let g = build !mtypes_ref in
				og_ref := Some g;
				g
		in
		let set_fn mtypes =
			og_ref := None;
			mtypes_ref := mtypes;
			mtypes
		in
		m.m_extra.m_agraph <- {build=build_fn; set_m_types=set_fn;};
		m
end


module Transitive = struct

type when_found_t = Type.tabstract -> Type.t list -> Type.tclass_field -> Type.texpr -> Type.t -> Common.pos -> Type.texpr

let find_with_graph og tleft tright p =
	let t = Common.timer ["AbstractTransitive";"resolve transitivity"] in
	let resolved =
    match og with
    | Some g ->
		let open AbstractGraph in
(*		Printf.printf "%s\n%!" (to_dot g); *)

		let visited_ref = ref [] in
		let visited t = if List.exists (fast_eq t) !visited_ref then true else (visited_ref := t::!visited_ref; false)  in
		(try
			let rec search tright acc =
				if visited tright then []
				else 
					try
						let succ = succs (follow tright) g in
						begin match succ with
						| (_, xs) when (!xs <> [])->
							let failed_ref = ref [] in
							begin try
								let rec find xs =
									match xs with
									| x::xs ->
										begin match x with
										| ToField((a, ap), tcf, r) ->
											(try
												ignore(unify_to_field a ap tright tcf);
												if (unify_to_field ~store_failed:failed_ref a ap tleft tcf) then (x, tleft)::acc
												else find xs
											with Not_found -> find xs)
										| To((a, ap), t, r) ->
											(try
												ignore(unify_to a ap tright t);
												if (unify_to ~store_failed:failed_ref a ap tleft t) then (x, tleft)::acc
												else find xs
											with Not_found -> find xs)
										| FromField((a, ap), tcf, r) ->
											(try
												ignore(unify_from_field a ap r tright tcf);
												if (unify_from_field ~store_failed:failed_ref a ap tright tleft tcf) then (x, tleft)::acc
												else find xs
											with Not_found -> find xs)
										| From((a, ap), t, r) ->
											(try 
												ignore(unify_from a ap r tright t);
												if (unify_from ~store_failed:failed_ref a ap tleft tright r) then (x, tleft)::acc
												else find xs
											with Not_found -> find xs)
										end
									| _ -> raise Not_found
								in 
								find !xs
							with Not_found ->
								let rec loop2 failed =
									match failed with
									| [] -> []
									| ((ge, td) as x)::xs ->
										(match search td (x::acc) with
										| (y::_) as ys -> ys
										| _ -> loop2 xs
										)
								in loop2 !failed_ref
							end
						| _ -> []
						end
					with Not_found -> []
			in search tright []
		with Not_found -> []
		)
    | None -> []
	in
	t();
	resolved

let find_with_graph_bak og tleft (*a2 tl2*) tright p =
	let t = Common.timer ["AbstractTransitive";"resolve transitivity"] in
	let resolved =
    match og with
    | Some g ->
		let open AbstractGraph in
		Printf.printf "%s\n%!" (to_dot g);

		let visited_ref = ref [] in
		let visited t = if List.exists (fast_eq t) !visited_ref then true else (visited_ref := t::!visited_ref; false)  in
		(try
			let rec search t1 tright acc =
				if visited t1 then []
				else 
					try
						let succ = succs t1 g in
						begin match succ with
						| (_, xs) when (!xs <> [])->
							let failed_ref = ref [] in
							begin try
								let rec find xs =
									match xs with
									| x::xs ->
										begin match x with
										| ToField((a, ap), tcf, r) -> 
											if (unify_to_field ~store_failed:failed_ref a ap tleft tcf) then (x, tleft)::acc
											else find xs
										| To((a, ap), t, r) ->
											if (unify_to ~store_failed:failed_ref a ap tleft t) then (x, tleft)::acc
											else find xs
										| FromField((a, ap), tcf, r) ->
											if (unify_from_field ~store_failed:failed_ref a ap t1 tright tcf) then (x, tleft)::acc
											else find xs
										| From((a, ap), t, r) ->
											if (unify_from ~store_failed:failed_ref a ap t1 tright t) then (x, tleft)::acc
											else find xs
										end
									| _ -> raise Not_found
								in 
								find !xs
							with Not_found ->
								let rec loop2 failed =
									match failed with
									| [] -> []
									| ((ge, td) as x)::xs ->
										begin match ge with
										| ToField(_, _, ts) | To(_, _, ts) | FromField(_, _, ts) | From(_, _, ts) ->
											(match search ts td (x::acc) with
											| (y::_) as ys -> ys
											| _ -> loop2 xs
											)
										end
								in loop2 !failed_ref
							end
						| _ -> []
						end
					with Not_found -> []
			in search tleft (follow tright) []
		with Not_found -> []
		)
    | None -> []
	in
	t();
	resolved

	let find_with_module m = find_with_graph (Some (m.m_extra.m_agraph.build()))

	let make_cast_with_graph og cast_stack (when_found:when_found_t) tleft (*a2 tl2*) eright p =
		let found = find_with_graph og tleft (*a2 tl2*) eright.etype p in
		match List.rev found with
		| [] -> raise Not_found
		| (x::xs) as lst ->
			let old_cast_stack = !cast_stack in
			(try
				let rec apply eright lst =
					(match lst with
					| (ge,tleft)::xs ->
						begin match ge with
						| ToField((a,tl),(t,cf),r) | FromField((a,tl),(t,cf),r) ->
							let e = when_found a tl cf eright r p in
							apply e xs
						| From(_, _, r) -> 
							apply (mk_cast eright r p) xs
						| To((a, tl), t, r) -> 
							apply(mk_cast eright r p) xs
						end
					| _ -> eright
					)
				in (apply eright lst)
			with Error(Custom "Recursive implicit cast", _) ->
				cast_stack := old_cast_stack;
				raise Not_found
			)	

	let make_cast_with_module m = make_cast_with_graph (Some (m.m_extra.m_agraph.build()))
end

let enter_class c cf =
	Refs.set_implicit_conversion_from_metas c.cl_meta;
	Refs.set_implicit_conversion_from_metas cf.cf_meta

module OnTheFly = struct
	let mk_sargs ?(sfx="") n l =
		let mk_arg i =
			let s_i = string_of_int i in
			let s = n ^ s_i in
			if sfx="" then s else s^sfx^s_i
		in
		let rec loop i acc =
			if i<=0 then acc
			else loop (i-1) ((mk_arg i) ::acc)
		in loop l []

	let create_type tname ctx code =
		let f = Printf.sprintf "%s.hx" tname in
		(*Printf.printf "Creating:%s\n%s\n%!" tname code;*)
		let p = { pfile=f; pmin=0; pmax=(String.length code); } in
		Parser.parse_string ctx code p Error.error true, tname, p

	let mk_OneOf ctx tname name arity =
		let s =
			match arity with
			| 0 -> "abstract OneOf0(Any) from Any {}"
			| 1 -> "abstract OneOf1<T>(T) from T to T {public inline function new(v:T) this=v;}"
			| _ ->
				let s_args ?(sfx="") ?(sep=",") n = String.concat sep (mk_sargs ~sfx:sfx n arity) in
				let tas = s_args "T" in
				let fps = s_args ~sep:" from " "T" in
				let from =
					if arity < 1 then ""
					else 
						let i = arity - 1 in
						(Printf.sprintf " from %s%i<%s> " name i (String.concat "," (mk_sargs "T" i)))
				in
				Printf.sprintf "@:allowUnderlyingType @:unorderedCheckTypeParameter @:coreType @:forward abstract %s<%s>(OneOf0) from %s%s {public inline function new(v:Any) this=v;}" tname tas fps from
		in
    	create_type tname ctx s
	
	let type_factories = [("OneOf", mk_OneOf)]

	let re_arity = Str.regexp "^\\([a-zA-Z_]+\\)\\([0-9]+\\)$"

	let get_arity s =
		ignore(Str.search_forward re_arity s 0);
		let i = Str.matched_group 2 s in
		let n = Str.matched_group 1 s in
		(n, int_of_string i)

	let find_type_factory s =
		let rec find xs =
			match xs with
			| (n,tf)::xs -> 
				if s=n then tf
				else find xs
			| [] -> raise Not_found
		in
		find type_factories

	let get_create_factory tname =
		let n,i = get_arity tname in
		let tf = find_type_factory n in
		n,i,tf

	let create_type ctx com tname error type_module =
		try
			let name, arity, factory = get_create_factory tname in
			let (pack, decls), cn, p = factory com tname name arity in
			type_module ctx ([], cn) p.pfile decls p
		with Not_found -> error()
end

module OneOf = struct
		let opt_args args ret = TFun(List.map(fun (n,o,t) -> n,true,t) args,ret)

		let opt_type t =
			match t with
			| TLazy f ->
				(!set_return_partial_type_ref) true;
				let t = (!f)() in
				(!set_return_partial_type_ref) false;
				t
			| _ ->
				t

		let find_field ctx should_access t fname p =
			let opt_args args ret = TFun(List.map(fun (n,o,t) -> n,true,t) args,ret) in
			let opt_type t =
				match t with
				| TLazy f ->
					(!set_return_partial_type_ref) true;
					let t = (!f)() in
					(!set_return_partial_type_ref) false;
					t
				| _ ->
					t
			in
			let rec get_fields t =
				match follow t with
				| TInst (c,params) ->
					let merge ?(cond=(fun _ -> true)) a b =
						PMap.foldi (fun k f m -> if cond f then PMap.add k f m else m) a b
					in
					let rec loop c params =
						let m = List.fold_left (fun m (i,params) ->
							merge m (loop i params)
						) PMap.empty c.cl_implements in
						let m = (match c.cl_super with
							| None -> m
							| Some (csup,cparams) -> merge m (loop csup cparams)
						) in
						let m = merge ~cond:(fun f -> should_access ctx c f false) c.cl_fields m in
						let m = (match c.cl_kind with
							| KTypeParameter pl -> List.fold_left (fun acc t -> merge acc (get_fields t)) m pl
							| _ -> m
						) in
						PMap.map (fun f -> { f with cf_type = apply_params c.cl_params params (opt_type f.cf_type); cf_public = true; }) m
					in
					loop c params
				| TAbstract({a_impl = Some c} as a,pl) ->
					let fields = try
						let _,el,_ = Meta.get Meta.Forward a.a_meta in
						let sl = ExtList.List.filter_map (fun e -> match fst e with
							| EConst(Ident s) -> Some s
							| _ -> None
						) el in
						let fields =
							match a.a_this with
							| TAbstract({a_path=([],"OneOf0"); _}, _) ->
								(match a.a_path with
								| [], "OneOf1" -> get_fields (List.hd pl)
								| _ ->
									let m_fields = List.map (fun t ->
										get_fields t
									) pl in
									match m_fields with
									| m::ms ->
										let rec eq ms k cf1 nm =
											match ms with
											| [] ->
												PMap.add k cf1 nm
											| m'::ms' ->
												(try
													let cf2 = PMap.find k m' in
													if type_iseq cf1.cf_type cf2.cf_type then
														eq ms' k cf1 nm
													else 
														PMap.remove k nm
												with
													| Not_found -> PMap.remove k nm
												)
										in
										PMap.foldi (eq ms) m m
									| _ -> raise Not_found
								)
							| _ -> get_fields (apply_params a.a_params pl a.a_this)
						in
						if sl = [] then fields else PMap.fold (fun cf acc ->
							if List.mem cf.cf_name sl then
								PMap.add cf.cf_name cf acc
							else
								acc
						) fields PMap.empty
					with Not_found ->
						PMap.empty
					in
					PMap.fold (fun f acc ->
						if f.cf_name <> "_new" && should_access ctx c f true && Meta.has Meta.Impl f.cf_meta && not (Meta.has Meta.Enum f.cf_meta) then begin
							let f = (!prepare_using_field_ref) f in
							let t = apply_params a.a_params pl (follow f.cf_type) in
							PMap.add f.cf_name { f with cf_public = true; cf_type = opt_type t } acc
						end else
							acc
					) c.cl_statics fields
				| TAnon a ->
					(match !(a.a_status) with
					| Statics c ->
						let is_abstract_impl = match c.cl_kind with KAbstractImpl _ -> true | _ -> false in
						let pm = match c.cl_constructor with None -> PMap.empty | Some cf -> PMap.add "new" cf PMap.empty in
						PMap.fold (fun f acc ->
							if should_access ctx c f true && (not is_abstract_impl || not (Meta.has Meta.Impl f.cf_meta) || Meta.has Meta.Enum f.cf_meta) then
								PMap.add f.cf_name { f with cf_public = true; cf_type = opt_type f.cf_type } acc else acc
						) a.a_fields pm
					| _ ->
						a.a_fields)
				| TFun (args,ret) ->
					let t = opt_args args ret in
					let cf = mk_field "bind" (tfun [t] t) p null_pos in
					PMap.add "bind" cf PMap.empty
				| _ ->
					PMap.empty
			in
			let fields = get_fields t in
			PMap.find fname fields
end

module Implicit = struct
	exception Found of texpr

	let show_implicits implicits =
		List.iter (fun fe -> let e = fe([]) in Printf.printf "%s\n%!" ((!Refs.format_ref) ((Ast.s_expr e)) (pos e))) implicits

	let get_implicit_param n meta =
		List.find (fun m ->
		match m with
		| Meta.ImplicitParam,[EConst(Ident s), _],_ when s=n -> true
		| _ -> false
		) meta

	let extract_call ((e,p) as ep) = match e with
		| ECall(e, _) -> e
		| _ -> ep

	let update_call ((e,p) as ep) = match e with
		| EBlock(e::es) -> EBlock((extract_call e)::es),p
		| _ -> extract_call ep

	let search_and_allocate load_instance locals cast_or_unify_raise type_expr type_against t implicits =
		(*Printf.printf "search for implicit %s through :\n" (s_type_kind t);
		show_implicits implicits;*)
		
		let unify_raise e =
			let et = type_expr e in
			let et = cast_or_unify_raise t et et.epos in
			raise (Found et)
		in

		let unify =  match t with
			| TFun (args, r) ->
				let eargs = List.map (fun (s,o,t) -> EConst(Ident "null"),null_pos ) args in
				let unify fe =
					let e = update_call (fe eargs) in
					unify_raise e
				in
				unify
			| _ -> 
				let unify fe =
					let e = fe [] in
					let e = (match e with 
					| EConst(Ident s), _ ->
						let ov = try Some(PMap.find s locals) with Not_found ->None in
						(match ov with 
						| None -> () 
						| Some v -> if not (Meta.has Meta.Implicit v.v_meta) then raise Not_found
						);
						e
					| _ ->
						let rec loop e =
							match e with
								| ENew ((tp, p) as tpp, args), pe when (List.length tp.tparams)=0 ->
									let ti = load_instance tpp true p in
									let e =
										(match ti with
										| TInst (tc, pms) when (List.length pms) > 0 ->
											let et = type_against ti (EConst(Ident "null"), p) in
											(cast_or_unify_raise t et et.epos);
											(match follow et.etype with
											| TInst(tc, pms) as ti ->
												ENew(((match (try TExprToExpr.convert_type ti with Exit -> TExprToExpr.convert_type (TInst (tc,[]))) with CTPath ctp -> ctp, p | _ -> assert false)), args), pe
											| _ -> raise Not_found
											)								
										| _ -> e
										)
									in e
								| EBlock(x::xs), pb -> EBlock((loop x)::xs), pb
								| _ -> e
						in loop e
					) 
					in
					unify_raise e
				in
				unify
		in
		let unify f = try unify f with Found _ as f -> raise f | _ -> () in 
		try
			List.iter (unify) implicits;
			raise Not_found
		with Found e -> e

	let resolver load_instance cast_or_unify_raise type_expr type_against =
		(fun t locals implicits ->
			search_and_allocate load_instance locals cast_or_unify_raise type_expr type_against t implicits 
		)
end