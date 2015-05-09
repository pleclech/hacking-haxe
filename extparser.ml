open Ast

let use_extended_syntax = ref false

let warning : (string -> pos -> unit) ref = ref (fun _ _ -> assert false)

let mk_efield e n p = EField (e, n), p
let mk_eblock b p = EBlock b, p
let mk_eident n p = (EConst(Ident n), p)
let mk_estring n p = (EConst(String n), p)
let mk_eint i p = (EConst(Int (string_of_int i)), p)
let mk_mconst p = (Meta.Const, [], p)

type 'a stream_state = {
	mutable ss_q: 'a Queue.t; (* priority queue *)
	mutable ss_q_cnt:int; (* peek count *)
	mutable ss_is:'a Stream.t; (* input token stream *)
	mutable ss_is_cnt:int; (* peek count *)
	mutable ss_os:'a Stream.t; (* output stream : mixed of queue and stream *)
	mutable ss_os_cnt:int; (* output stream discarded count *)
	mutable ss_itq_cnt:int; (* number of priority token in the queue *)
	mutable ss_itp_cnt:int; (* number of priority token in the peek buffer *)
}

let ss:(token*pos) stream_state option ref = ref None

let dump_token ?(pfx="") ?(sfx="") ls =
	let rp = ref null_pos in
	let s = String.concat " " (List.map (fun (t, p) -> rp:=p; s_token t) ls) in
	!warning (pfx^s^sfx) !rp

let insert_token (ts:(token*pos) list) =
	match !ss with
	| None -> ()
	| Some ss ->
		let rec scopy i s q =
			if i > 0 then begin
				Queue.push (Stream.next s) q;
				scopy (i-1) s q
			end
		in
		let qcopy i q1 q2 =
			if i > 0 && q1!=q2 then
				let rec loop i =
					if i > 0 then begin
						Queue.push (Queue.pop q1) q2;
						loop (i-1)
					end
				in loop i
		in
		let consumed =  (Stream.count ss.ss_os - ss.ss_os_cnt) in
		let pb_cnt =
			let i = ss.ss_itp_cnt - consumed in
			ss.ss_itp_cnt <- if i <= 0 then 0 else i;
			let t = ss.ss_is_cnt + ss.ss_q_cnt - consumed in
			if t <= 0 then 0 else t
		in
		let q1 = ss.ss_q in
		let itp_cnt = ss.ss_itp_cnt in
		let itq_cnt = ss.ss_itq_cnt in
		(*let s = Printf.sprintf "pbc:%d cfc:%d kqc:%d sc:%d oc:%d itq:%d itp:%d" pb_cnt itp_cnt itq_cnt (Stream.count ss.ss_os) ss.ss_os_cnt ss.ss_itq_cnt ss.ss_itp_cnt
		in !warning s null_pos;*)
		let q2 = if (Queue.length q1)<>itq_cnt then Queue.create() else q1 in
		scopy itp_cnt ss.ss_os q2;
		ss.ss_itq_cnt <- ss.ss_itq_cnt + itp_cnt;
		qcopy itq_cnt q1 q2;
		List.iter (fun t -> Queue.push t q2) ts;
		ss.ss_itq_cnt <- ss.ss_itq_cnt + (List.length ts);
		scopy (pb_cnt-itp_cnt) ss.ss_os q2;
		if q1!=q2 then begin
			qcopy (Queue.length q1) q1 q2;
			ss.ss_q <- q2;
		end;
		ss.ss_q_cnt <- 0;
		ss.ss_is_cnt <- 0;
		ss.ss_itp_cnt <- 0;
		(*dump_token ~pfx:("after queue("^(string_of_int ss.ss_itq_cnt)^") ") (List.rev (Queue.fold (fun t a -> a::t) [] ss.ss_q));*)
		ss.ss_os_cnt <- Stream.count ss.ss_os

let expr_q = Queue.create()

let insert_expr ?(with_semi=true) (e:expr) =
		Queue.push e expr_q;
		if with_semi then insert_token [Semicolon, pos e]

let token_stream stream =
	let tq = Queue.create() in
	let st = {ss_q=tq; ss_q_cnt=0; ss_is=stream; ss_is_cnt=0; ss_os=stream; ss_os_cnt=0; ss_itq_cnt=0; ss_itp_cnt=0; } in
	let next ss i =
		let t =
			if Queue.is_empty ss.ss_q then begin
				ss.ss_is_cnt <- ss.ss_is_cnt + 1;
				Stream.next ss.ss_is
			end else begin
				ss.ss_q_cnt <- ss.ss_q_cnt + 1;
				ss.ss_is_cnt <- 0;
				if ss.ss_itq_cnt > 0 then begin
					ss.ss_itq_cnt <- ss.ss_itq_cnt - 1;
					ss.ss_itp_cnt <- ss.ss_itp_cnt + 1;
				end;
				Queue.pop ss.ss_q
			end
		in
		Some t
	in
	let s = Stream.from (next st) in
	st.ss_os <- s;
	ss := Some st;
	s

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


let to_pseudo_private cn fl =
	let tfr_field cf =
		if Meta.has Meta.Private cf.cff_meta then begin
			let ac = APrivate::(List.filter(fun c -> (c<>APrivate)&&(c<>APublic)) cf.cff_access) in
			cf.cff_access <- ac;
			cf.cff_meta <- (Meta.Native, [mk_estring ("_"^(String.lowercase cn)^"_"^cf.cff_name) cf.cff_pos], cf.cff_pos)::cf.cff_meta;
		end
	in List.iter tfr_field fl

let for_ctx = ref []
let push_for_ctx (a:expr option) = for_ctx := a :: !for_ctx
let pop_for_ctx() = match !for_ctx with
	| [] -> ()
	| x::xs -> for_ctx := xs
let peek_for_ctx() = match !for_ctx with
	| [] -> None
	| x::xs -> x

let dequeue_expr hx s =
	if Queue.is_empty expr_q then
		hx s
	else
		Queue.pop expr_q