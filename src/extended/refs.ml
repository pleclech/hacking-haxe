open Ast
open Globals

type token_stream_t = (token * pos) Stream.t

type var_arg_t = (placed_name * type_hint option * expr option)

let warning_ref : (string -> pos -> unit) ref = ref (fun _ _ -> assert false)
let make_binop_ref:(binop -> expr -> expr -> expr) ref = ref (fun _ _ _ -> assert false)
let parse_meta_ref:(?is_const:bool -> token_stream_t -> metadata) ref = ref (fun ?is_const _ -> assert false)
let dollar_ident_ref:(token_stream_t -> placed_name) ref = ref (fun _ -> assert false)
let parse_fun_param_value_ref:(token_stream_t -> expr option) ref = ref (fun _ -> assert false)
let parse_type_opt_ref:(token_stream_t -> type_hint option) ref = ref (fun _ -> assert false)
let parse_call_params_ref:((expr list -> pos -> expr) -> pos -> token_stream_t -> expr) ref = ref (fun _ _ _ -> assert false)
let parse_class_fields_ref:(bool -> pos -> token_stream_t -> class_field list*pos) ref = ref ( fun _ _ _ -> assert false)
let parse_var_decl_ref:(?is_const:bool -> token_stream_t -> var_arg_t) ref = ref ( fun ?is_const _ -> assert false)
let parse_var_decls_ref:(?is_const:bool -> pos -> token_stream_t -> var_arg_t list) ref = ref ( fun ?is_const _ _ -> assert false)
let expr_next_ref:(expr -> token_stream_t -> expr) ref = ref ( fun _ _ -> assert false)
let expr_ref:(?flags:int -> token_stream_t -> expr) ref = ref (fun ?flags _ -> assert false)
let parse_constraint_params_ref:(token_stream_t -> type_param list) ref = ref (fun _ -> assert false)
let parse_fun_param_ref:(token_stream_t -> (placed_name * bool * metadata * type_hint option * expr option) ) ref = ref (fun _ -> assert false)

let attach_meta_to_expr metas expr =
    let to_emeta meta = EMeta(meta, (EBreak, null_pos)), null_pos in
    match metas with
    | [] -> expr
    | (_, _, p)::xs -> EMeta ((Meta.MetaList, List.map to_emeta metas, p), expr), punion p (pos expr)

let attach_meta_to_optexpr metas oexpr =
    if metas=[] then
        oexpr
    else
        let expr = match oexpr with
            | Some e -> e
            | None -> (EConst (Ident "null"), null_pos)
        in
        Some (attach_meta_to_expr metas expr)

let unattach_meta_from_expr expr =
    let to_meta (emeta, _) =
        match emeta with
        | EMeta(meta, (EBreak, _)) -> meta
        | _ -> Meta.Last, [], null_pos
    in
    match expr with
    | EMeta ((Meta.MetaList, emetas, _), e), _ -> List.map to_meta emetas, e
    | _ -> [], expr

let unattach_meta_from_optexpr oexpr = match oexpr with
    | None -> [], None
    | Some e ->
        let m,e = unattach_meta_from_expr e in
        m, Some e
