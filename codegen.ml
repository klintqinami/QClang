(* Code generation: translate takes a semantically checked AST and
produces QASM
*)

(* We'll refer to Llvm and Ast constructs with module names *)
open Ast
open Sast 

module StringMap = Map.Make(String)

type value =
    VInt of int
  | VBool of bool
  | VFloat of float
  | VNoexpr

type stmt_val =
    VNone
  | VReturn of value

type environment = value StringMap.t

let unwrap_int = function
    env, VInt(i) -> env, i
  | _ -> raise (Failure "missing int")
  
let unwrap_float = function
    env, VFloat(f) -> env, f
  | _ -> raise (Failure "missing int")

let unwrap_bool = function
    env, VBool(b) -> env, b
  | _ -> raise (Failure "missing int")

let default_val = function
    Int -> VInt 0
  | Bool -> VBool false
  | Float -> VFloat 0.
  | Void -> VNoexpr

(* Code Generation from the SAST. Returns an LLVM module if successful,
   throws an exception if something is wrong. *)
let translate functions =
  let function_map = List.fold_left (fun map fdecl ->
    StringMap.add fdecl.sfname fdecl map) StringMap.empty functions
  in

  let rec eval_expr env (_, expr) = match expr with
      SLiteral(i) -> env, VInt i
    | SFliteral(s) -> env, VFloat (float_of_string s)
    | SBoolLit(b) -> env, VBool b
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
          | And -> VBool(e1' && e1')
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
        env, eval_func name args
    | SNoexpr -> env, VNoexpr

  and

  eval_stmts env slist =
    List.fold_left (fun (env, sv) stmt ->
        if sv = VNone then eval_stmt env stmt else env, sv)
    (env, VNone) slist

  and

  eval_stmt env = function
      SBlock(lst) -> eval_stmts env lst
    | SExpr(expr) ->
        let env, _ = eval_expr env expr in
        env, VNone
    | SIf(cond, thn, els) ->
        let env, cond' = unwrap_bool (eval_expr env cond) in
        eval_stmt env (if cond' then thn else els)
    | SFor(init, test, final, body) ->
        let env, _ = eval_expr env init in
        let rec eval_body env =
          let env, test' = unwrap_bool (eval_expr env test) in
          if test' then
            let env, sv = eval_stmt env body in
            if sv = VNone then
              let env, _ = eval_expr env final in
              eval_body env
            else
              env, sv
          else
            env, VNone
        in eval_body env
    | SWhile(cond, body) ->
        let rec eval_body env =
          let env, cond' = unwrap_bool (eval_expr env cond) in
          if cond' then
            let env, sv = eval_stmt env body in
            if sv = VNone then eval_body env else env, sv
          else
            env, VNone
        in eval_body env
    | SReturn(expr) ->
        let env, ret = eval_expr env expr in
        env, VReturn ret

  and
      
  eval_func name args =
    let func = StringMap.find name function_map in
    let env = List.fold_left2 (fun env (_, name) arg ->
      StringMap.add name arg env) StringMap.empty func.sformals args in
    let env = List.fold_left (fun env (typ, name) ->
      StringMap.add name (default_val typ) env) env func.slocals in
    let _, sv = eval_stmts env func.sbody in
    match sv with
        VNone -> VNoexpr
      | VReturn v -> v
  in
    

  print_string "OPENQASM 2.0;\n";
  ignore (eval_func "main" [])
