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

let rec attach_meta_to_expr metas expr =
    if metas=[] then
        expr
    else
    match metas with
    | [] -> expr
    | (_, _, p) as meta::xs ->
        let rec mk_emeta metas ((v, pv) as e) =
            match metas with
            | [] -> e
            | (_,_,p) as meta::xs -> mk_emeta xs (EMeta (meta, e), punion p pv)
        in
        let rec loop ((v, pv) as e) =
            match v with
            | EBinop ((OpAssign | OpAssignOp _),_,_) -> mk_emeta xs (EMeta (meta, e), punion p pv)
            | EBinop (bop,e1,e2) -> EBinop (bop, loop e1, e2) , punion p pv
            | ETernary (e1,e2,e3) -> ETernary (loop e1, e2, e3), punion p pv
            | _ -> mk_emeta xs (EMeta (meta, e), punion p pv)
        in attach_meta_to_expr xs (loop expr)

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
    let rec loop expr acc =
        match expr with
        | EMeta (m, e), _ -> loop e (m::acc)
        | _ -> acc, expr
    in
    loop expr []

let unattach_meta_from_optexpr oexpr = match oexpr with
    | None -> [], None
    | Some e ->
        let m,e = unattach_meta_from_expr e in
        m, Some e
