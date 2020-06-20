(****************************************************************
 * ASL interactive frontend
 *
 * Copyright Arm Limited (c) 2017-2019
 * SPDX-Licence-Identifier: BSD-3-Clause
 ****************************************************************)

(** ASL interactive frontend *)

open LibASL

open Asl_ast
open Asl_visitor

open Yojson

module Parser = Asl_parser
module TC     = Tcheck
module PP     = Asl_parser_pp
module AST    = Asl_ast

let opt_filenames : string list ref = ref []
let opt_print_version = ref false
let opt_verbose = ref false


let help_msg = [
    {|:? :help                       Show this help message|};
    {|:elf <file>                    Load an ELF file|};
    {|:opcode <instr-set> <int>      Decode and execute opcode|};
    {|:project <file>                Execute ASLi commands in <file>|};
    {|:q :quit                       Exit the interpreter|};
    {|:run                           Execute instructions|};
    {|:set impdef <string> = <expr>  Define implementation defined behavior|};
    {|:set +<flag>                   Set flag|};
    {|:set -<flag>                   Clear flag|};
    {|<expr>                         Execute ASL expression|};
    {|<stmt> ;                       Execute ASL statement|}
]

let flags = [
    ("trace:write", Eval.trace_write);
    ("trace:fun",   Eval.trace_funcall);
    ("trace:prim",  Eval.trace_primop);
    ("trace:instr", Eval.trace_instruction)
]

let mkLoc (fname: string) (input: string): AST.l =
    let len = String.length input in
    let start : Lexing.position = { pos_fname = fname; pos_lnum = 1; pos_bol = 0; pos_cnum = 0 } in
    let finish: Lexing.position = { pos_fname = fname; pos_lnum = 1; pos_bol = 0; pos_cnum = len } in
    AST.Range (start, finish)

let rec process_command (tcenv: TC.Env.t) (cpu: Cpu.cpu) (fname: string) (input0: string): unit =
    let input = String.trim input0 in
    (match String.split_on_char ' ' input with
    | [""] ->
        ()
    | [":elf"; file] ->
        Printf.printf "Loading ELF file %s.\n" file;
        let entry = Elf.load_file file cpu.elfwrite in
        Printf.printf "Entry point = 0x%Lx\n" entry
    | [":help"] | [":?"] ->
        List.iter print_endline help_msg;
        print_endline "\nFlags:";
        List.iter (fun (nm, v) -> Printf.printf "  %s%s\n" (if !v then "+" else "-") nm) flags
    | [":opcode"; iset; opcode] ->
        (* todo: make this code more robust *)
        let op = Z.of_int (int_of_string opcode) in
        Printf.printf "Decoding and executing instruction %s %s\n" iset (Z.format "%x" op);
        cpu.opcode iset op
    | (":set" :: "impdef" :: rest) ->
        let cmd = String.concat " " rest in
        let loc = mkLoc fname cmd in
        let (x, e) = LoadASL.read_impdef tcenv loc cmd in
        let v = Eval.eval_expr loc cpu.env e in
        Eval.Env.setImpdef cpu.env x v
    | [":set"; flag] when Utils.startswith flag "+" ->
        (match List.assoc_opt (Utils.stringDrop 1 flag) flags with
        | None -> Printf.printf "Unknown flag %s\n" flag;
        | Some f -> f := true
        )
    | [":set"; flag] when Utils.startswith flag "-" ->
        (match List.assoc_opt (Utils.stringDrop 1 flag) flags with
        | None -> Printf.printf "Unknown flag %s\n" flag;
        | Some f -> f := false
        )
    | [":project"; prj] ->
        let inchan = open_in prj in
        (try
            while true do
                process_command tcenv cpu prj (input_line inchan)
            done
        with
        | End_of_file ->
            close_in inchan
        )
    | [":q"] | [":quit"] ->
        exit 0
    | [":run"] ->
        (try
            while true do
                cpu.step ()
            done
        with
        | Value.Throw (_, Primops.Exc_ExceptionTaken) ->
            Printf.printf "Exception taken\n"
        )
    | _ ->
        if ';' = String.get input (String.length input - 1) then begin
            let s = LoadASL.read_stmt tcenv input in
            Eval.eval_stmt cpu.env s
        end else begin
            let loc = mkLoc fname input in
            let e   = LoadASL.read_expr tcenv loc input in
            let v   = Eval.eval_expr loc cpu.env e in
            print_endline (Value.pp_value v)
        end
    )

let rec repl (tcenv: TC.Env.t) (cpu: Cpu.cpu): unit =
    flush stdout;
    (match LNoise.linenoise "ASLi> " with
    | None -> ()
    | Some input ->
        LNoise.history_add input |> ignore;
        (try
            LoadASL.report_eval_error (fun _ -> ()) (fun _ ->
                LoadASL.report_type_error (fun _ -> ()) (fun _ ->
                    LoadASL.report_parse_error (fun _ -> ()) (fun _ ->
                        process_command tcenv cpu "<stdin>" input
                    )
                )
            )
        with
        | exc ->
            Printf.printf "  Error %s\n" (Printexc.to_string exc);
            Printexc.print_backtrace stdout
        );
        repl tcenv cpu
    )

let ts str = `String str
let ti i = `Int i
let tl l = `List l
let tnl name l = `List ([ ts name ] @ l)

let rec cident (ident: ident) = match ident with
    | Ident(x) -> tnl "Ident" [ts x]
    | FIdent(x, i) -> tnl "FIdent" [ts x ; ti i]

and ce_elsif x = match x with E_Elsif_Cond(cond, _then) -> tl [ cexpr cond ; cexpr _then ]

and cexpr (expr: expr) = match expr with
    | Expr_If(cond, _then, elsifs, _else) -> tnl "Expr_If" [cexpr cond ; cexpr _then ; tl (List.map ce_elsif elsifs) ; cexpr _else]
    | Expr_Binop(a, binop, b) -> tnl "Expr_Binop" [cexpr a ; cbinop binop ; cexpr b]
    | Expr_Unop(unop, a) -> tnl "Expr_Binop" [cunop unop ; cexpr a]
    | Expr_Field(expr, ident) -> tnl "Expr_Field" [cexpr expr ; cident ident]
    | Expr_Fields(expr, idents) -> tnl "Expr_Fields" [cexpr expr ; tl (List.map cident idents)]
    | Expr_Slices(expr, slices) -> tnl "Expr_Slices" [cexpr expr ; tl (List.map cslice slices)]
    | Expr_In(expr, pattern) -> tnl "Expr_In" [cexpr expr ; cpattern pattern]
    | Expr_Var(ident) -> tnl "Expr_Var" [cident ident]
    | Expr_Parens(expr) -> tnl "Expr_Parens" [cexpr expr]
    | Expr_Tuple(exprs) -> tnl "Expr_Tuple" (List.map cexpr exprs)
    | Expr_Unknown(ty) -> tnl "Expr_Unknown" [ctype ty]
    | Expr_ImpDef(ty, ostr) -> tnl "Expr_ImpDef" [ctype ty ; (match ostr with Some(str) -> ts str | None -> `Null)]
    | Expr_TApply(ident, texprs, pexprs) -> tnl "Expr_TApply" [cident ident ; tl (List.map cexpr texprs) ; tl (List.map cexpr pexprs)]
    | Expr_Array(a, b) -> tnl "Expr_Array" [cexpr a ; cexpr b]
    | Expr_LitInt(x) -> tnl "Expr_LitInt" [ts x]
    | Expr_LitHex(x) -> tnl "Expr_LitHex" [ts x]
    | Expr_LitReal(x) -> tnl "Expr_LitReal" [ts x]
    | Expr_LitBits(x) -> tnl "Expr_LitBits" [ts x]
    | Expr_LitMask(x) -> tnl "Expr_LitMask" [ts x]
    | Expr_LitString(x) -> tnl "Expr_LitString" [ts x]

and cslice slice = match slice with
    | Slice_Single(expr) -> tnl "Slice_Single" [cexpr expr]
    | Slice_HiLo(a, b) -> tnl "Slice_HiLo" [cexpr a ; cexpr b]
    | Slice_LoWd(a, b) -> tnl "Slice_LoWd" [cexpr a ; cexpr b]

and csi x = tl [tl (List.map cslice (fst x)) ; cident (snd x)]

and cixtype ixtype = match ixtype with
    | Index_Enum(ident) -> tnl "Index_Enum" [cident ident]
    | Index_Range(a, b) -> tnl "Index_Range" [cexpr a ; cexpr b]

and ctype (ty: ty) = match ty with
    | Type_Constructor(ident) -> tnl "Type_Constructor" [cident ident]
    | Type_Bits(expr) -> tnl "Type_Bits" [cexpr expr]
    | Type_App(ident, exprs) -> tnl "Type_App" [cident ident ; tl (List.map cexpr exprs)]
    | Type_OfExpr(expr) -> tnl "Type_OfExpr" [cexpr expr]
    | Type_Register(il, sil) -> tnl "Type_Register" [ts il ; tl (List.map csi sil)]
    | Type_Array(ixtype, ty) -> tnl "Type_Array" [cixtype ixtype ; ctype ty]
    | Type_Tuple(tys) -> tnl "Type_Tuple" (List.map ctype tys)

and ctvp x = tl [ ctype (fst x) ; cident (snd x) ]

and clexpr lexpr = match lexpr with
    | LExpr_Wildcard -> tnl "LExpr_Wildcard" []
    | LExpr_Var(ident) -> tnl "LExpr_Var" [cident ident]
    | LExpr_Field(lexpr, ident) -> tnl "LExpr_Field" [clexpr lexpr ; cident ident]
    | LExpr_Fields(lexpr, idents) -> tnl "LExpr_Fields" [clexpr lexpr ; tl (List.map cident idents)]
    | LExpr_Slices(lexpr, slices) -> tnl "LExpr_Slices" [clexpr lexpr ; tl (List.map cslice slices)]
    | LExpr_BitTuple(lexprs) -> tnl "LExpr_BitTuple" (List.map clexpr lexprs)
    | LExpr_Tuple(lexprs) -> tnl "LExpr_Tuple" (List.map clexpr lexprs)
    | LExpr_Array(lexpr, expr) -> tnl "LExpr_Array" [clexpr lexpr ; cexpr expr]
    | LExpr_Write(ident, texprs, pexprs) -> tnl "LExpr_Write" [cident ident ; tl (List.map cexpr texprs) ; tl (List.map cexpr pexprs)]
    | LExpr_ReadWrite(ident, identb, texprs, pexprs) -> tnl "LExpr_ReadWrite" [cident ident ; cident identb ; tl (List.map cexpr texprs) ; tl (List.map cexpr pexprs)]

and cs_elsif x = match x with S_Elsif_Cond(cond, _then) -> tl [cexpr cond ; tl (List.map cstmt _then)]

and calt x = match x with Alt_Alt(patterns, oexpr, stmts) -> tl [tl (List.map cpattern patterns) ; (match oexpr with Some(expr) -> cexpr expr | None -> `Null) ; tl (List.map cstmt stmts)]

and cdirection x = match x with Direction_Up -> ts "Direction_Up" | Direction_Down -> ts "Direction_Down"

and ccatcher x = match x with Catcher_Guarded(expr, stmts) -> tnl "Catcher_Guarded" [cexpr expr ; tl (List.map cstmt stmts)]

and cstmt stmt = match stmt with
    | Stmt_VarDeclsNoInit(ty, idents, _) -> tnl "Stmt_VarDeclsNoInit" [ctype ty ; tl (List.map cident idents)]
    | Stmt_VarDecl(ty, ident, expr, _) -> tnl "Stmt_VarDecl" [ctype ty ; cident ident ; cexpr expr]
    | Stmt_ConstDecl(ty, ident, expr, _) -> tnl "Stmt_ConstDecl" [ctype ty ; cident ident ; cexpr expr]
    | Stmt_Assign(lexpr, expr, _) -> tnl "Stmt_Assign" [clexpr lexpr ; cexpr expr]
    | Stmt_FunReturn(expr, _) -> tnl "Stmt_FunReturn" [cexpr expr]
    | Stmt_ProcReturn(_) -> tnl "Stmt_ProcReturn" []
    | Stmt_Assert(expr, _) -> tnl "Stmt_Assert" [cexpr expr]
    | Stmt_Unpred(_) -> tnl "Stmt_Unpred" []
    | Stmt_ConstrainedUnpred(_) -> tnl "Stmt_ConstrainedUnpred" []
    | Stmt_ImpDef(ident, _) -> tnl "Stmt_ImpDef" [cident ident]
    | Stmt_Undefined(_) -> tnl "Stmt_Undefined" []
    | Stmt_ExceptionTaken(_) -> tnl "Stmt_ExceptionTaken" []
    | Stmt_Dep_Unpred(_) -> tnl "Stmt_Dep_Unpred" []
    | Stmt_Dep_ImpDef(str, _) -> tnl "Stmt_Dep_ImpDef" [ts str]
    | Stmt_Dep_Undefined(_) -> tnl "Stmt_Dep_Undefined" []
    | Stmt_See(expr, _) -> tnl "Stmt_See" [cexpr expr]
    | Stmt_Throw(ident, _) -> tnl "Stmt_Throw" [cident ident]
    | Stmt_DecodeExecute(ident, expr, _) -> tnl "Stmt_DecodeExecute" [cident ident ; cexpr expr]
    | Stmt_TCall(ident, texprs, pexprs, _) -> tnl "Stmt_TCall" [cident ident ; tl (List.map cexpr texprs) ; tl (List.map cexpr pexprs)]
    | Stmt_If(cond, _then, elsifs, _else, _) -> tnl "Stmt_If" [cexpr cond ; tl (List.map cstmt _then) ; tl (List.map cs_elsif elsifs) ; tl (List.map cstmt _else)]
    | Stmt_Case(expr, alts, ostmts, _) -> tnl "Stmt_Case" [cexpr expr ; tl (List.map calt alts) ; (match ostmts with Some(stmts) -> tl (List.map cstmt stmts) | None -> `Null)]
    | Stmt_For(ident, a, dir, b, stmts, _) -> tnl "Stmt_For" [cident ident ; cexpr a ; cdirection dir ; cexpr b ; tl (List.map cstmt stmts)]
    | Stmt_While(expr, stmts, _) -> tnl "Stmt_While" [cexpr expr ; tl (List.map cstmt stmts)]
    | Stmt_Repeat(stmts, expr, _) -> tnl "Stmt_Repeat" [tl (List.map cstmt stmts) ; cexpr expr]
    | Stmt_Try(stmts, ident, catchers, ostmts, _) -> tnl "Stmt_Try" [tl (List.map cstmt stmts) ; cident ident ; tl (List.map ccatcher catchers) ; (match ostmts with Some(estmts) -> tl (List.map cstmt estmts) | None -> `Null)]

and csformal sformal = match sformal with
    | Formal_In(ty, ident) -> tnl "Formal_In" [ctype ty ; cident ident]
    | Formal_InOut(ty, ident) -> tnl "Formal_InOut" [ctype ty ; cident ident]

and cinstr_field x = match x with IField_Field(ident, a, b) -> tnl "IField_Field" [cident ident ; ti a ; ti b]

and copcode_value x = match x with
    | Opcode_Bits(lit) -> tnl "Opcode_Bits" [ts lit]
    | Opcode_Mask(lit) -> tnl "Opcode_Mask" [ts lit]

and cbits x = match x with (a, b) -> tl [ti a ; ts b]

and cencoding encoding = match encoding with
    | Encoding_Block(identa, identb, instr_fields, opcode_value, expr, bitsList, stmts, _) ->
        tnl "Encoding_Block" [cident identa ; cident identb ; tl (List.map cinstr_field instr_fields) ; copcode_value opcode_value ; cexpr expr ; tl (List.map cbits bitsList) ; tl (List.map cstmt stmts)]

and cdecode_pattern pattern = match pattern with
    | DecoderPattern_Bits(lit) -> tnl "DecoderPattern_Bits" [ts lit]
    | DecoderPattern_Mask(lit) -> tnl "DecoderPattern_Mask" [ts lit]
    | DecoderPattern_Wildcard(ident) -> tnl "DecoderPattern_Wildcard" [cident ident]
    | DecoderPattern_Not(decode_pattern) -> tnl "DecoderPattern_Not" [cdecode_pattern decode_pattern]

and cdecode_slice slice = match slice with
    | DecoderSlice_Slice(a, b) -> tnl "DecoderSlice_Slice" [ti a ; ti b]
    | DecoderSlice_FieldName(ident) -> tnl "DecoderSlice_FieldName" [cident ident]
    | DecoderSlice_Concat(idents) -> tnl "DecoderSlice_Concat" (List.map cident idents)

and cdecode_alt alt = match alt with DecoderAlt_Alt(decode_patterns, decode_body) -> tnl "DecoderAlt_Alt" [tl (List.map cdecode_pattern decode_patterns) ; cdecode_body decode_body]

and cdecode_body body = match body with
    | DecoderBody_UNPRED(_) -> tnl "DecoderBody_UNPRED" []
    | DecoderBody_UNALLOC(_) -> tnl "DecoderBody_UNALLOC" []
    | DecoderBody_NOP(_) -> tnl "DecoderBody_NOP" []
    | DecoderBody_Encoding(ident, _) -> tnl "DecoderBody_Encoding" [cident ident]
    | DecoderBody_Decoder(instr_fields, decode_case, _) -> tnl "DecoderBody_Decoder" [tl (List.map cinstr_field instr_fields) ; cdecode_case decode_case]

and cdecode_case decode_case = match decode_case with
    | DecoderCase_Case(decode_slices, decode_alts, _) -> tnl "DecoderCase_Case" [tl (List.map cdecode_slice decode_slices) ; tl (List.map cdecode_alt decode_alts)]

and cunop unop = match unop with
    | Unop_Negate -> tnl "Unop_Negate" []
    | Unop_BoolNot -> tnl "Unop_BoolNot" []
    | Unop_BitsNot -> tnl "Unop_BitsNot" []

and cbinop binop = match binop with
    | Binop_Eq -> tnl "Binop_Eq" []
    | Binop_NtEq -> tnl "Binop_NtEq" []
    | Binop_Gt -> tnl "Binop_Gt" []
    | Binop_GtEq -> tnl "Binop_GtEq" []
    | Binop_Lt -> tnl "Binop_Lt" []
    | Binop_LtEq -> tnl "Binop_LtEq" []
    | Binop_Plus -> tnl "Binop_Plus" []
    | Binop_Minus -> tnl "Binop_Minus" []
    | Binop_Multiply -> tnl "Binop_Multiply" []
    | Binop_Divide -> tnl "Binop_Divide" []
    | Binop_Power -> tnl "Binop_Power" []
    | Binop_Quot -> tnl "Binop_Quot" []
    | Binop_Rem -> tnl "Binop_Rem" []
    | Binop_Div -> tnl "Binop_Div" []
    | Binop_Mod -> tnl "Binop_Mod" []
    | Binop_ShiftL -> tnl "Binop_ShiftL" []
    | Binop_ShiftR -> tnl "Binop_ShiftR" []
    | Binop_BoolAnd -> tnl "Binop_BoolAnd" []
    | Binop_BoolOr -> tnl "Binop_BoolOr" []
    | Binop_BoolIff -> tnl "Binop_BoolIff" []
    | Binop_BoolImplies -> tnl "Binop_BoolImplies" []
    | Binop_BitOr -> tnl "Binop_BitOr" []
    | Binop_BitEor -> tnl "Binop_BitEor" []
    | Binop_BitAnd -> tnl "Binop_BitAnd" []
    | Binop_Append -> tnl "Binop_Append" []
    | Binop_Concat -> tnl "Binop_Concat" []
    | Binop_DUMMY -> tnl "Binop_DUMMY" []

and cmapfield mapfield = match mapfield with
    | MapField_Field(ident, pattern) -> tnl "MapField_Field" [cident ident ; cpattern pattern]

and cpattern pattern = match pattern with
    | Pat_LitInt(lit) -> tnl "Pat_LitInt" [ts lit]
    | Pat_LitHex(lit) -> tnl "Pat_LitHex" [ts lit]
    | Pat_LitBits(lit) -> tnl "Pat_LitBits" [ts lit]
    | Pat_LitMask(lit) -> tnl "Pat_LitMask" [ts lit]
    | Pat_Const(ident) -> tnl "Pat_Const" [cident ident]
    | Pat_Wildcard -> tnl "Pat_Wildcard" []
    | Pat_Tuple(patterns) -> tnl "Pat_Tuple" (List.map cpattern patterns)
    | Pat_Set(patterns) -> tnl "Pat_Set" (List.map cpattern patterns)
    | Pat_Range(a, b) -> tnl "Pat_Range" [cexpr a ; cexpr b]
    | Pat_Single(expr) -> tnl "Pat_Single" [cexpr expr]

and cdecl (decl: declaration) = match decl with
    | Decl_BuiltinType(v, _) -> tnl "Decl_BuiltinType" [cident v]
    | Decl_Forward(name, _) -> tnl "Decl_Forward" [cident name]
    | Decl_Record(name, tvps, _) -> tnl "Decl_Record" [cident name ; tl (List.map ctvp tvps)]
    | Decl_Typedef(name, ty, _) -> tnl "Decl_Typedef" [cident name ; ctype ty]
    | Decl_Enum(name, values, _) -> tnl "Decl_Enum" (List.map cident values)
    | Decl_Var(ty, name, _) -> tnl "Decl_Var" [ctype ty ; cident name]
    | Decl_Const(ty, ident, expr, _) -> tnl "Decl_Const" [ctype ty ; cident ident ; cexpr expr]
    | Decl_BuiltinFunction(ty, ident, tvps, _) -> tnl "Decl_BuiltinFunction" [ctype ty ; cident ident ; tl (List.map ctvp tvps)]
    | Decl_FunType(ty, ident, tvps, _) -> tnl "Decl_FunType" [ctype ty ; cident ident ; tl (List.map ctvp tvps)]
    | Decl_FunDefn(ty, ident, tvps, stmts, _) -> tnl "Decl_FunDefn" [ctype ty ; cident ident ; tl (List.map ctvp tvps) ; tl (List.map cstmt stmts)]
    | Decl_ProcType(ident, tvps, _) -> tnl "Decl_ProcType" [cident ident ; tl (List.map ctvp tvps)]
    | Decl_ProcDefn(ident, tvps, stmts, _) -> tnl "Decl_ProcType" [cident ident ; tl (List.map ctvp tvps) ; tl (List.map cstmt stmts)]
    | Decl_VarGetterType(ty, ident, _) -> tnl "Decl_VarGetterType" [ctype ty ; cident ident]
    | Decl_VarGetterDefn(ty, ident, stmts, _) -> tnl "Decl_VarGetterType" [ctype ty ; cident ident ; tl (List.map cstmt stmts)]
    | Decl_ArrayGetterType(ty, ident, tvps, _) -> tnl "Decl_ArrayGetterType" [ctype ty ; cident ident ; tl (List.map ctvp tvps)]
    | Decl_ArrayGetterDefn(ty, ident, tvps, stmts, _) -> tnl "Decl_ArrayGetterDefn" [ctype ty ; cident ident ; tl (List.map ctvp tvps) ; tl (List.map cstmt stmts)]
    | Decl_VarSetterType(aident, ty, ident, _) -> tnl "Decl_VarSetterType" [cident aident ; ctype ty ; cident ident]
    | Decl_VarSetterDefn(aident, ty, ident, stmts, _) -> tnl "Decl_VarSetterType" [cident aident ; ctype ty ; cident ident ; tl (List.map cstmt stmts)]
    | Decl_ArraySetterType(aident, formals, ty, ident, _) -> tnl "Decl_ArraySetterType" [cident aident ; tl (List.map csformal formals) ; ctype ty ; cident ident]
    | Decl_ArraySetterDefn(aident, formals, ty, ident, stmts, _) -> tnl "Decl_ArraySetterDefn" [cident aident ; tl (List.map csformal formals) ; ctype ty ; cident ident ; tl (List.map cstmt stmts)]
    | Decl_InstructionDefn(ident, encodings, ostmts, b, stmts, _) ->
        (match ostmts with
            | Some(opstmts) -> tnl "Decl_InstructionDefn" [cident ident ; tl (List.map cencoding encodings) ; tl (List.map cstmt opstmts) ; `Bool b ; tl (List.map cstmt stmts)]
            | None -> tnl "Decl_InstructionDefn" [cident ident ; tl (List.map cencoding encodings) ; `Null ; `Bool b ; tl (List.map cstmt stmts)])
    | Decl_DecoderDefn(ident, decode_case, _) -> tnl "Decl_DecoderDefn" [cident ident ; cdecode_case decode_case]
    | Decl_Operator1(unop, idents, _) -> tnl "Decl_Operator1" [cunop unop ; tl (List.map cident idents)]
    | Decl_Operator2(binop, idents, _) -> tnl "Decl_Operator1" [cbinop binop ; tl (List.map cident idents)]
    | Decl_NewEventDefn(ident, tvps, _) -> tnl "Decl_NewEventDefn" [cident ident ; tl (List.map ctvp tvps)]
    | Decl_EventClause(ident, stmts, _) -> tnl "Decl_EventClause" [cident ident ; tl (List.map cstmt stmts)]
    | Decl_NewMapDefn(ty, ident, tvps, stmts, _) -> tnl "Decl_NewMapDefn" [ctype ty ; cident ident ; tl (List.map ctvp tvps) ; tl (List.map cstmt stmts)]
    | Decl_MapClause(ident, mapfields, oexpr, stmts, _) ->
        (match oexpr with
            | Some(expr) -> tnl "Decl_MapClause" [cident ident ; tl (List.map cmapfield mapfields) ; cexpr expr ; tl (List.map cstmt stmts)]
            | None -> tnl "Decl_MapClause" [cident ident ; tl (List.map cmapfield mapfields) ; `Null ; tl (List.map cstmt stmts)])
    | Decl_Config(ty, ident, expr, _) -> tnl "Decl_Config" [ctype ty ; cident ident ; cexpr expr]

let dumpAst decls: unit =
    print_endline (Yojson.Basic.pretty_to_string (`List (List.map cdecl decls)))

let options = Arg.align ([
    ( "-v", Arg.Set opt_verbose,              "       Verbose output");
    ( "--version", Arg.Set opt_print_version, "       Print version");
] )

let version = "ASL 0.2.0 alpha"

let banner = [
    {|            _____  _       _    ___________________________________|};
    {|    /\     / ____|| |     (_)   ASL interpreter                    |};
    {|   /  \   | (___  | |      _    Copyright Arm Limited (c) 2017-2019|};
    {|  / /\ \   \___ \ | |     | |                                      |};
    {| / ____ \  ____) || |____ | |   |} ^ version;
    {|/_/    \_\|_____/ |______||_|   ___________________________________|}
]
let usage_msg =
    ( version
    ^ "\nusage: asl <options> <file1> ... <fileN>\n"
    )

let _ =
  Arg.parse options
    (fun s -> opt_filenames := (!opt_filenames) @ [s])
    usage_msg

let main () =
    if !opt_print_version then Printf.printf "%s\n" version
    else begin
        (*List.iter print_endline banner;
        print_endline "\nType :? for help";*)
        let t  = LoadASL.read_file "prelude.asl" true !opt_verbose in
        let ts = List.map (fun filename ->
            if Utils.endswith filename ".spec" then begin
                LoadASL.read_spec filename !opt_verbose
            end else if Utils.endswith filename ".asl" then begin
                LoadASL.read_file filename false !opt_verbose
            end else begin
                failwith ("Unrecognized file suffix on "^filename)
            end
        ) !opt_filenames
        in

        dumpAst (List.concat (t::ts));

        (*if !opt_verbose then Printf.printf "Building evaluation environment\n";
        let env = (try
            Eval.build_evaluation_environment (List.concat (t::ts))
        with
        | Value.EvalError (loc, msg) ->
            Printf.printf "  %s: Evaluation error: %s\n" (pp_loc loc) msg;
            exit 1
        ) in
        if !opt_verbose then Printf.printf "Built evaluation environment\n";

        LNoise.history_load ~filename:"asl_history" |> ignore;
        LNoise.history_set ~max_length:100 |> ignore;
        repl (TC.Env.mkEnv TC.env0) (Cpu.mkCPU env)*)
    end

let _ =ignore(main ())

(****************************************************************
 * End
 ****************************************************************)
