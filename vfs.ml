open String
open Str

type vfile = {
	buffer : Buffer.t;
	mutable mtime : float;
	mutable removed: bool;
}

type patch_action =
	| PatchDelete of char * int * int
	| PatchInsert of char * int * string
	| PatchClose

let memfiles:(string, vfile) Hashtbl.t = Hashtbl.create 0

let replace input output =
    global_replace (regexp_string input) output

let load_sys_file fn =
  let ch = open_in_bin fn in
  let n = in_channel_length ch in
  let b = Buffer.create n in
  Buffer.add_channel b ch n;
  close_in ch;
  b

let is_win() = match Sys.os_type with
	| "Win32" | "Cygwin" -> true
	| _ -> false

let get_filename = if is_win() then (fun fn -> lowercase fn) else (fun fn -> fn)

let get_full_path f = try Extc.get_full_path f with _ -> f

let unique_full_path = if is_win() then (fun f -> lowercase (get_full_path f)) else get_full_path

let get_path unique fn = not unique, if unique then unique_full_path fn else fn

let find_memfile ?(unique=true) fn =
	let _, fn = get_path unique fn in
	Hashtbl.find memfiles fn

let file_exists fn =
	try
		ignore(find_memfile fn);
		true
    with Not_found ->
    	Sys.file_exists fn

let is_removed fn =
	try
		let vf = find_memfile fn
		in vf.removed
	with Not_found -> false

let sys_mtime fn = try (Unix.stat fn).Unix.st_mtime with _ -> 0.

let stat_mtime ?(unique=true) fn =
	let unique, fn = get_path unique fn in
	try
		let vf = find_memfile ~unique:unique fn in
		let mt = vf.mtime in
		if vf.removed then
			let smt = sys_mtime fn in
			if smt > mt then begin
				Hashtbl.remove memfiles fn;
				smt
			end else
				mt  
		else
			mt
    with Not_found -> sys_mtime fn

let update_buffer ?(unique=true) fn buffer =
	let _, fn = get_path unique fn in
	let vf = {buffer=buffer; mtime=Unix.time(); removed=is_removed fn} in
	Hashtbl.add memfiles fn vf;
	vf

let create_mem_file ?(unique=true) ?(buffer=None) fn =
	let unique, fn = get_path unique fn in
	match buffer with
	| Some buffer -> update_buffer ~unique:unique fn buffer
	| None ->
	    	try
	    		find_memfile ~unique:unique fn
	    	with Not_found ->
	    		update_buffer ~unique:unique fn (Buffer.create 0)

let create_from_file ?(unique=true) fn =
	let unique, fn = get_path unique fn in
	let buffer = (try load_sys_file fn with _ -> Buffer.create 0) in
	update_buffer ~unique:unique fn buffer

let update_if_removed ?(unique=true) fn vf =
	if vf.removed then
		let unique, fn = get_path unique fn in
		vf.removed <- false;
		create_from_file ~unique:unique fn 
	else
		vf

let mem_remove ?(unique=true) fn =
	let _, fn = get_path unique fn in
	try
		let vf = Hashtbl.find memfiles fn in
		vf.removed <- true;
		Buffer.clear vf.buffer
	with Not_found -> ()

let buffer_delete vf_buffer pos len =
	let buf_len = (Buffer.length vf_buffer) in
	let len = if (len = -1) then buf_len - pos else len in
	let buf_len = buf_len - len in
	let buffer = Buffer.create buf_len in
	(if pos > 0 then Buffer.add_string buffer (Buffer.sub vf_buffer 0 pos));
	Buffer.add_string buffer (Buffer.sub vf_buffer (pos + len) (buf_len-pos));
	buffer

let mem_delete ?(unique=true) fn pos len =
	let unique, fn = get_path unique fn in
	if (pos=0) && (len = -1) then
		update_buffer ~unique:unique fn (Buffer.create 0)
	else
		let vf = 
			try
				let vf = find_memfile ~unique:unique fn in
				update_if_removed fn vf
			with Not_found -> create_from_file ~unique:unique fn
		in
		try
			update_buffer ~unique:unique fn (buffer_delete vf.buffer pos len)
		with _ -> failwith (Printf.sprintf "Could not patch delete %d,%d of %s" pos len fn)


let buffer_insert vf_buffer pos content =
	let buf_len = Buffer.length vf_buffer in
	if pos==0 then
		let buffer = Buffer.create ((length content) + buf_len) in
		Buffer.add_string buffer content;
		Buffer.add_string buffer (Buffer.contents vf_buffer);
		buffer
	else if pos==buf_len then begin
		Buffer.add_string vf_buffer content;
		vf_buffer
	end else
		let buffer = Buffer.create ((length content) + buf_len) in
		(if pos > 0 then Buffer.add_string buffer (Buffer.sub vf_buffer 0 pos));
		Buffer.add_string buffer content;
		Buffer.add_string buffer (Buffer.sub vf_buffer pos (buf_len - pos));
		buffer

let mem_insert ?(unique=true) fn pos content =
	let unique, fn = get_path unique fn in
	let vf =
		try
			let vf = find_memfile ~unique:unique fn in
			update_if_removed fn vf
		with Not_found -> create_from_file ~unique:unique fn
	in
	try
		update_buffer ~unique:unique fn (buffer_insert vf.buffer pos content)
	with _ -> failwith (Printf.sprintf "Could not patch insert %d,%s of %s" pos content fn)

let apply_patch ?(unique=true) ?(text_before="") fn action =
	let unique, fn = get_path unique fn in
	let get_pos_len =
		let txt_len = length text_before in
		if txt_len=0 then (fun bc pos len -> pos, len)
		else 
			(fun bc pos len ->
				if bc='b' then pos, len
				else UTF8.nth text_before pos, if len > 0 then UTF8.nth (sub text_before pos (txt_len-pos)) len else len)
	in
	match action with
	| PatchDelete (byte_or_char, pos, len) ->
		let pos,len = get_pos_len byte_or_char pos len in
		ignore(mem_delete ~unique:unique fn pos len)
	| PatchInsert (byte_or_char, pos, code) ->
		let pos, _ = get_pos_len byte_or_char pos 0 in
		ignore(mem_insert ~unique:unique fn pos code)
	| PatchClose -> mem_remove ~unique:unique fn

let apply_patchs ?(unique=true) (fn, actions) =
	let unique, fn = get_path unique fn in
	let vf = 
		try
			let vf = find_memfile ~unique:unique fn in
			update_if_removed fn vf
		with Not_found -> create_from_file ~unique:unique fn
	in
	let rbuf = ref (vf.buffer) in
	let rcpos = ref 0 in
	let rbpos = ref 0 in
	let byte_offset cpos clen =
		let bpos = !rbpos in
		let blen = (Buffer.length !rbuf) - bpos in
		let dcpos = cpos - !rcpos in
		let txt = Buffer.sub !rbuf bpos blen in
		let bpos =
			if dcpos=0 then dcpos
			else UTF8.nth txt dcpos
		in
		let blen = if clen > 0 then UTF8.nth (sub txt bpos (blen - bpos)) clen else 0 in
		let bpos = !rbpos + bpos in
		rbpos := bpos;
		rcpos := cpos;
		bpos, blen
	in

	List.iter(fun a -> match a with
		| PatchDelete('c', cpos, clen) ->
			let bpos, blen = byte_offset cpos clen in
			(try
				let buffer = buffer_delete !rbuf bpos blen in
				ignore(update_buffer ~unique:unique fn buffer);
				rbuf := buffer
			with _ -> failwith (Printf.sprintf "Could not patch delete %d,%d of %s" cpos clen fn))
		| PatchInsert('c', cpos, content) ->
			let bpos, _ = byte_offset cpos 0 in
			(try
				let buffer = buffer_insert !rbuf bpos content in
				ignore(update_buffer ~unique:unique fn buffer);
				rbuf := buffer;
			with _ -> failwith (Printf.sprintf "Could not patch insert %d,%s of %s" cpos content fn))
		| _ -> apply_patch ~unique:unique fn a
	) actions

let mem_stream fn =
	let vf = find_memfile fn in
	if vf.removed then raise Not_found
	else
		let pos = ref 0 in
		fun b c ->
			let buf = vf.buffer in
			let len = Buffer.length buf in
			let p = !pos in
			let avail = len - p in
			if avail <= 0 then 0
			else begin
				let read = if c >= avail then avail else c in
				let read =
					try
						Buffer.blit buf p b 0 read;
						read
					with _ ->
						0
				in
				pos := p + read;
				read
			end

(*
	[bc] indicate if position and length are in byte or characters
	[+-] indicate if we want delete (-) or insert (+)
	next group is the position in the source
	next group is length if it's a delete operation otherwise it's the text to be inserted 
*)
let re_patch_action = Str.regexp "@\\([bc]\\)\\([+-]\\)\\([0-9]+\\):\\([^\001]+\\)\001"

let make_patchs fn sargs len =
		let rec loop str len actions =
			try
				if len < 3 then
					str, len, (fn, List.rev actions)
				else
					let s = sub str 0 3 in
					if s="@x\001" then begin
						mem_remove fn;
						let len = len - 3 in
						if len > 0 then
							loop (sub str 3 len) len (PatchClose::actions)
						else
							"", 0, (fn, List.rev (PatchClose::actions))
					end else
					if string_match re_patch_action str 0 then begin
						let byte_or_char = matched_group 1 str in
						let op = matched_group 2 str in
						let pos = int_of_string (matched_group 3 str) in
						let len_or_code = matched_group 4 str in
						let action =
							(match op with
								| "-" ->
									(try
										let len = int_of_string len_or_code in
										PatchDelete (byte_or_char.[0], pos, len)
									with
										| (Failure _) as err -> raise err
										| _ -> failwith ("invalid length for patch delete : " ^ len_or_code))
								| "+" ->
									PatchInsert (byte_or_char.[0], pos, len_or_code)
								| _ -> failwith ("invalid patch operation : " ^ op)
							)
						in
						let gpos = (group_end 4) + 1 in
						let len = len - gpos in
						let str =
							if len > 0 then
								sub str gpos len
							else
								""
						in
						loop str len (action::actions)
					end else str, len, (fn, List.rev actions)
			with
				| (Failure _) as err -> raise err
				| _ -> failwith ("invalid patch : " ^ fn)
		in
		loop sargs len []
