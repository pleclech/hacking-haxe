open Ast
open Globals

	type 'a stream_state_t = {
		mutable ss_q: 'a Queue.t; (* priority queue *)
		mutable ss_q_cnt:int; (* peek count *)
		mutable ss_is:'a Stream.t; (* input token stream *)
		mutable ss_is_cnt:int; (* peek count *)
		mutable ss_os:'a Stream.t; (* output stream : mixed of queue and stream *)
		mutable ss_os_cnt:int; (* output stream discarded count *)
		mutable ss_itq_cnt:int; (* number of priority token in the queue *)
		mutable ss_itp_cnt:int; (* number of priority token in the peek buffer *)
	}

	let make_stream_state stream =
		let tq = Queue.create() in
			{ss_q=tq; ss_q_cnt=0; ss_is=stream; ss_is_cnt=0; ss_os=stream; ss_os_cnt=0; ss_itq_cnt=0; ss_itp_cnt=0; }

	let ss:(token * pos) stream_state_t option ref = ref None

	let insert_token (ts:(token * pos) list) =
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
			ss.ss_os_cnt <- Stream.count ss.ss_os


	let token_stream stream =
		let st = make_stream_state stream in
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
