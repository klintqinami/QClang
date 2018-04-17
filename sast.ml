(* Semantically-checked Abstract Syntax Tree and functions for printing it *)

open Ast

type sexpr = typ * sx
and sx =
    SLiteral of int
  | SFliteral of string
  | SBoolLit of bool
  | STupleLit of sexpr list 
  | SId of string
  | SBinop of sexpr * op * sexpr
  | SUnop of uop * sexpr
  | SAssign of string * sexpr
  | SCall of string * sexpr list
  | SNoexpr

type jump =
    SReturnJump of sexpr
  | SJump of block ref
  | SCondJump of sexpr * block ref * block ref
and block = sexpr list * jump

module BlockMap = Map.Make(struct type t = block ref let compare = compare end)

type sstmt =
    SIf of sexpr * sstmt * sstmt
  | SFor of sexpr * sexpr * sexpr * sstmt
  | SWhile of sexpr * sstmt
  | SBlock of sstmt list
  | SExpr of sexpr
  | SReturn of sexpr

type sfunc_decl = {
    styp : typ;
    sfname : string;
    sformals : bind list;
    slocals : bind list;
    sbody : block;
  }

type sprogram = sfunc_decl list

(* Pretty-printing functions *)

let rec string_of_sexpr (t, e) =
  "(" ^ string_of_typ t ^ " : " ^ (match e with
    SLiteral(l) -> string_of_int l
  | SBoolLit(true) -> "true"
  | SBoolLit(false) -> "false"
  | SFliteral(l) -> l
  | SId(s) -> s
  | SBinop(e1, o, e2) ->
      string_of_sexpr e1 ^ " " ^ string_of_op o ^ " " ^ string_of_sexpr e2
  | SUnop(o, e) -> string_of_uop o ^ string_of_sexpr e
  | SAssign(v, e) -> v ^ " = " ^ string_of_sexpr e
  | SCall(f, el) ->
      f ^ "(" ^ String.concat ", " (List.map string_of_sexpr el) ^ ")"
  | STupleLit(el) -> "(" ^ String.concat ", " (List.map string_of_sexpr el) ^ ")"
  | SNoexpr -> ""
				  ) ^ ")"				     

let rec string_of_sstmt = function
    SBlock(stmts) ->
      "{\n" ^ String.concat "" (List.map string_of_sstmt stmts) ^ "}\n"
  | SExpr(expr) -> string_of_sexpr expr ^ ";\n";
  | SReturn(expr) -> "return " ^ string_of_sexpr expr ^ ";\n";
  | SIf(e, s, SBlock([])) ->
      "if (" ^ string_of_sexpr e ^ ")\n" ^ string_of_sstmt s
  | SIf(e, s1, s2) ->  "if (" ^ string_of_sexpr e ^ ")\n" ^
      string_of_sstmt s1 ^ "else\n" ^ string_of_sstmt s2
  | SFor(e1, e2, e3, s) ->
      "for (" ^ string_of_sexpr e1  ^ " ; " ^ string_of_sexpr e2 ^ " ; " ^
      string_of_sexpr e3  ^ ") " ^ string_of_sstmt s
  | SWhile(e, s) -> "while (" ^ string_of_sexpr e ^ ") " ^ string_of_sstmt s


let string_of_block block =
  let get_block_name (names, id) block =
    if BlockMap.mem block names then
      BlockMap.find block names, (names, id)
    else
      let name = string_of_int id in
      name, (BlockMap.add block name names, id + 1)
  in
  let rec string_of_block' block names visited =
    if BlockMap.mem block visited then "", names, visited else
    let slist, jump = !block in
    let name, names = get_block_name names block in
    let visited = BlockMap.add block () visited in
    let start =  name ^ ":\n" ^
    String.concat "\n" (List.map string_of_sexpr slist) ^ "\n" in
    match jump with
        SReturnJump(e) -> (start ^ "return " ^ string_of_sexpr e ^ ";\n"), names, visited
      | SJump(dest) ->
          let dest_name, names = get_block_name names dest in
          let dest_str, names, visited = string_of_block' dest names visited in
          start ^ "jump " ^ dest_name ^ ";\n" ^ dest_str, names, visited
      | SCondJump(cond, dest1, dest2) ->
          let dest1_name, names = get_block_name names dest1 in
          let dest2_name, names = get_block_name names dest2 in
          let dest1_str, names, visited = string_of_block' dest1 names visited in
          let dest2_str, names, visited = string_of_block' dest2 names visited in
          start ^ "cond_jump " ^ (string_of_sexpr cond) ^ ", " ^
          dest1_name ^ ", " ^ dest2_name ^ ";\n" ^ dest1_str ^ dest2_str,
          names, visited
  in
  let block_ref = ref block in
  let str, _, _ = string_of_block' block_ref (BlockMap.empty, 0) BlockMap.empty in str

let string_of_sfdecl fdecl =
  string_of_typ fdecl.styp ^ " " ^
  fdecl.sfname ^ "(" ^ String.concat ", " (List.map snd fdecl.sformals) ^
  ")\n{\n" ^
  String.concat "" (List.map string_of_vdecl fdecl.slocals) ^
  string_of_block fdecl.sbody ^
  "}\n"

let string_of_sprogram funcs =
  String.concat "\n" (List.map string_of_sfdecl funcs)
