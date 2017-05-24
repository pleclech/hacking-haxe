
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

let mk_sarg ?(sfx="") ?(sep=",") n l = String.concat sep (mk_sargs ~sfx:sfx n l)
