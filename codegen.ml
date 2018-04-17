(* Code generation: translate takes a semantically checked AST and produces 
 * QASM *)

open Ast
open Sast 

module StringMap = Map.Make(String)

type value =
    VInt of int
  | VBool of bool
  | VFloat of float
  | VQubit
  | VTuple of value list
  | VNoexpr

type environment = value StringMap.t

let unwrap_int = function
    env, VInt(i) -> env, i
  | _ -> raise (Failure "missing int")
  
let unwrap_float = function
    env, VFloat(f) -> env, f
  | _ -> raise (Failure "missing float")

let unwrap_bool = function
    env, VBool(b) -> env, b
  | _ -> raise (Failure "missing bool")
 
let rec default_val = function
    Int -> VInt 0
  | Bool -> VBool false
  | Float -> VFloat 0.
  | Qubit -> VQubit 
  | Tuple(el) -> VTuple (List.map default_val el)
  | Void -> VNoexpr

(* Code Generation from the SAST. Returns OpenQASM IR if successful,
   throws an exception if something is wrong. *)
let translate functions =
  let function_map = List.fold_left (fun map fdecl ->
    StringMap.add fdecl.sfname fdecl map) StringMap.empty functions
  in

  let rec eval_expr env (_, expr) = match expr with
      SLiteral(i) -> env, VInt i
    | SFliteral(s) -> env, VFloat (float_of_string s)
    | SBoolLit(b) -> env, VBool b
    | STupleLit(el) ->  
        let env, args = List.fold_right (fun e (env, args) ->
          let env, arg = eval_expr env e in (env, arg :: args))
             el (env, []) in env, VTuple args
    | SId(n) -> env, StringMap.find n env
    | SBinop(((Int, _) as e1), op, ((Int, _) as e2)) ->
        let env, e1' = unwrap_int (eval_expr env e1) in
        let env, e2' = unwrap_int (eval_expr env e2) in
        (env, match op with 
            Add -> VInt(e1' + e2')
          | Sub -> VInt(e1' - e2')
          | Mult -> VInt(e1' * e2')
          | Div -> VInt(e1' / e2')
          | Equal -> VBool(e1' = e2')
          | Neq -> VBool(e1' <> e2')
          | Less -> VBool(e1' < e2')
          | Leq -> VBool(e1' <= e2')
          | Greater -> VBool(e1' > e2')
          | Geq -> VBool(e1' >= e2')
          | And -> VInt(e1' land e2')
          | Or -> VInt(e1' lor e2')
        )
    | SBinop(((Float, _) as e1), op, ((Float, _) as e2)) ->
        let env, e1' = unwrap_float (eval_expr env e1) in
        let env, e2' = unwrap_float (eval_expr env e2) in
        (env, match op with 
            Add -> VFloat(e1' +. e2')
          | Sub -> VFloat(e1' -. e2')
          | Mult -> VFloat(e1' *. e2')
          | Div -> VFloat(e1' /. e2')
          | Equal -> VBool(e1' = e2')
          | Neq -> VBool(e1' <> e2')
          | Less -> VBool(e1' < e2')
          | Leq -> VBool(e1' <= e2')
          | Greater -> VBool(e1' > e2')
          | Geq -> VBool(e1' >= e2')
          | _ -> raise (Failure "bad op")
        )
    | SBinop(((Bool, _) as e1), op, ((Bool, _) as e2)) ->
        let env, e1' = unwrap_bool (eval_expr env e1) in
        let env, e2' = unwrap_bool (eval_expr env e2) in
        (env, match op with 
            Equal -> VBool(e1' = e2')
          | Neq -> VBool(e1' != e2')
          | And -> VBool(e1' && e2')
          | Or -> VBool(e1' || e2')
          | _ -> raise (Failure "bad op")
        )
    | SBinop(_, _, _) -> raise (Failure "sounds like trouble")
    | SUnop(op, ((Int, _) as e)) ->
        let env, e' = unwrap_int (eval_expr env e) in
        (env, match op with
            Neg -> VInt(-e')
          | _ -> raise (Failure "bad op")
        )
    | SUnop(op, ((Float, _) as e)) ->
        let env, e' = unwrap_float (eval_expr env e) in
        (env, match op with
            Neg -> VFloat(-. e')
          | _ -> raise (Failure "bad op")
        )
    | SUnop(op, ((Bool, _) as e)) ->
        let env, e' = unwrap_bool (eval_expr env e) in
        (env, match op with
            Not -> VBool(not e')
          | _ -> raise (Failure "bad op")
        )
    | SUnop(_, _) -> raise (Failure "sounds like trouble")
    | SAssign(name, e) ->
        let env, e' = eval_expr env e in
        (StringMap.add name e' env, e')
    | SCall(name, es) ->
        let env, args = List.fold_right (fun e (env, args) ->
          let env, arg = eval_expr env e in (env, arg :: args))
        es (env, []) in
        (match name, args with
            "print", [VInt i] ->
              print_string ("// " ^ string_of_int i ^ "\n"); env, VNoexpr
          | "printb", [VBool b] ->
              print_string ("// " ^ string_of_int (if b then 1 else 0) ^ "\n");
              env, VNoexpr
          | "printf", [VFloat f] ->
              print_string ("// " ^ string_of_float f ^ "\n"); env, VNoexpr
          | _ -> env, eval_func name args)
    | SNoexpr -> env, VNoexpr

  and

  eval_block env (stmts, term) =
    let env = List.fold_left (fun env expr ->
      let env, _ = eval_expr env expr in env)
    env stmts in
    match term with
        SReturnJump e -> snd (eval_expr env e)
      | SJump b -> eval_block env !b
      | SCondJump(cond, thn, els) ->
          let env, cond' = unwrap_bool (eval_expr env cond) in
          if cond' then eval_block env !thn else eval_block env !els

  and
      
  eval_func name args =
    let func = StringMap.find name function_map in
    let env = List.fold_left2 (fun env (_, name) arg ->
      StringMap.add name arg env) StringMap.empty func.sformals args in
    let env = List.fold_left (fun env (typ, name) ->
      StringMap.add name (default_val typ) env) env func.slocals in
    eval_block env func.sbody
  in

  (* Temporary minimal circuit for testing *)
  print_string "OPENQASM 2.0;\n";
  print_string "include \"qelib1.inc\";\n";
  print_string "qreg q[1];\n";
  print_string "creg c[1];\n";
  print_string "h q;\n";

  ignore (eval_func "main" [])
