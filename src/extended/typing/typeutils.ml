open Globals

let create_type tname ctx code =
	let f = Printf.sprintf "%s.hx" tname in
	(*Printf.printf "Creating:%s\n%s\n%!" tname code;*)
	let p = { pfile=f; pmin=0; pmax=(String.length code); } in
	Parser.parse_string ctx code p Error.error true, tname, p
