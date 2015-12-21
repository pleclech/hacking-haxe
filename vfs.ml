open String
open Str

type vfile = {
	buffer : Buffer.t;
	mutable mtime : float;
	mutable removed: bool;
}

type patch_action =
	| PatchDelete of int * int
	| PatchInsert of int * string
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

let stat_mtime fn =
	try
		let vf = find_memfile fn in
		let mt = vf.mtime in
		if vf.removed then
			let smt = sys_mtime fn in
			if smt >= mt then begin
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
	let buffer = (try load_sys_file fn with _ -> failwith ("Could not load " ^ fn)) in
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
		vf.mtime <- Unix.time();
		Buffer.clear vf.buffer
	with Not_found -> ()

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
			let buf_len = (Buffer.length vf.buffer) in
			let len = if (len = -1) then buf_len - pos else len in
			let buf_len = buf_len - len in
			let buffer = Buffer.create buf_len in
			(if pos > 0 then Buffer.add_string buffer (Buffer.sub vf.buffer 0 pos));
			Buffer.add_string buffer (Buffer.sub vf.buffer (pos + len) (buf_len-pos));
			update_buffer ~unique:unique fn buffer
		with _ -> failwith ("Could not patch delete " ^ fn)

let mem_insert ?(unique=true) fn pos content =
	let unique, fn = get_path unique fn in
	let vf =
		try
			let vf = find_memfile ~unique:unique fn in
			update_if_removed fn vf
		with Not_found -> create_from_file ~unique:unique fn
	in
	let buf_len = Buffer.length vf.buffer in
	if pos > buf_len then
		failwith (Printf.sprintf "Invalid patch insert pos:%d for %s" pos fn)
	else
		let vf = 
			if pos==0 then
				let buffer = Buffer.create ((length content) + buf_len) in
				Buffer.add_string buffer content;
				Buffer.add_string buffer (Buffer.contents vf.buffer);
				update_buffer ~unique:unique fn buffer
			else if pos==buf_len then begin
				Buffer.add_string vf.buffer content;
				vf
			end else
				let buffer = Buffer.create ((length content) + buf_len) in
				(if pos > 0 then Buffer.add_string buffer (Buffer.sub vf.buffer 0 pos));
				Buffer.add_string buffer content;
				Buffer.add_string buffer (Buffer.sub vf.buffer pos (buf_len - pos));
				update_buffer ~unique:unique fn buffer
		in
		vf

let apply_patch ?(unique=true) fn action =
	let unique, fn = get_path unique fn in
	match action with
	| PatchDelete (pos, len) -> ignore(mem_delete ~unique:unique fn pos len)
	| PatchInsert (pos, code) -> ignore(mem_insert ~unique:unique fn pos code)
	| PatchClose -> mem_remove ~unique:unique fn

let apply_patchs ?(unique=true) (fn, actions) =
	let unique, fn = get_path unique fn in
	List.iter(fun a -> apply_patch ~unique:unique fn a) actions

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

let re_patch_action = Str.regexp "@\\(+\\|-\\)\\([0-9]+\\):\\([^\001]+\\)\001"

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
						let op = matched_group 1 str in
						let pos = int_of_string (matched_group 2 str) in
						let len_or_code = matched_group 3 str in
						let action =
							(match op with
								| "-" ->
									(try
										let len = int_of_string len_or_code in
										PatchDelete (pos, len)
									with
										| (Failure _) as err -> raise err
										| _ -> failwith ("invalid length for patch delete : " ^ len_or_code))
								| "+" ->
									PatchInsert (pos, len_or_code)
								| _ -> failwith ("invalid patch operation : " ^ op)
							)
						in
						let gpos = (group_end 3) + 1 in
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
