(* Code generation: translate takes a semantically checked AST and produces 
 * QASM *)

open Ast
open Sast 

module StringMap = Map.Make(String)

type lvalue =
    LVId of string
  | LVTuple of lvalue * int
  | LVValue of value
and value =
    VInt of int
  | VBool of bool
  | VFloat of float
  | VQubit of string
  | VBit of string
  | VQubitInvalid of lvalue
  | VTuple of value list
  | VNoexpr

type stmt_val =
    VNone
  | VReturn of value

type environment = {
  name_map : value StringMap.t;
  counter : int;
}

let rec string_of_lval = function
    LVId(n) -> n
  | LVTuple(l, i) -> (string_of_lval l) ^ "[" ^ (string_of_int i) ^ "]"
  | LVValue _ -> raise (Failure "internal error")

let unwrap_int = function
    env, VInt(i) -> env, i
  | _ -> raise (Failure "internal error: missing int")
  
let unwrap_float = function
    env, VFloat(f) -> env, f
  | _ -> raise (Failure "internal error: missing float")

let unwrap_bool = function
    env, VBool(b) -> env, b
  | _ -> raise (Failure "internal error: missing bool")

let unwrap_tuple = function
    env, VTuple(t) -> env, t
  | _ -> raise (Failure "internal error: missing tuple")

let unwrap_bit = function
    env, VBit(b) -> env, b
  | _ -> raise (Failure "internal error: missing bit")

let unwrap_qubit = function
    env, VQubit(q) -> env, q
  | _, VQubitInvalid(var) ->
      raise (Failure ("qubit " ^ (string_of_lval var) ^ " used more than once"))
  | _ -> raise (Failure "internal error: missing qubit")
 
let rec default_val name env = function
    Int -> VInt 0
  | Bool -> VBool false
  | Float -> VFloat 0.
  | Qubit -> let qname = name ^ "_q" ^ string_of_int env.counter in
      print_string ("qreg " ^ qname ^ "[1];\n");
      VQubit (qname)
  | Bit -> let bname = name ^ "_b" ^ string_of_int env.counter in
      print_string ("creg " ^ bname ^ "[1];\n");
      VBit (bname)
  | Tuple(el) -> VTuple (List.mapi (fun i typ ->
      default_val (name ^ "_" ^ (string_of_int i)) env typ) el)
  | Void -> VNoexpr

(* Code Generation from the SAST. Returns OpenQASM IR if successful,
   throws an exception if something is wrong. *)
let translate functions =
  let function_map = List.fold_left (fun map fdecl ->
    StringMap.add fdecl.sfname fdecl map) StringMap.empty functions
  in

  (* convert an expression into an lvalue for loading/storing *)
  let rec eval_lval env ((_, e) as expr) = match e with
      SId(n) -> env, LVId n
    | _ -> let env, value = eval_expr env expr in
        (* by the semantic checker, we should only hit this on the RHS *)
        env, LVValue(value)
  and load_lval env = function
      LVId(s) -> StringMap.find s env.name_map
    | LVTuple(lval, idx) ->
        let _, value = unwrap_tuple (env, (load_lval env lval)) in
        List.nth value idx
    | LVValue(value) -> value
  and store_lval env value = function
      LVId(s) -> { env with name_map = StringMap.add s value env.name_map }
    | LVTuple(lval, idx) ->
        let env, old_val = unwrap_tuple (env, (load_lval env lval)) in
        let new_val = VTuple (List.mapi (fun i prev ->
          if i = idx then value else prev) old_val) in
        store_lval env new_val lval
    | LVValue _ -> env (* don't do anything if it's not actually an lvalue *)
  and eval_expr env (typ, expr) = match expr with
      SLiteral(i) -> env, VInt i
    | SFliteral(s) -> env, VFloat (float_of_string s)
    | SBoolLit(b) -> env, VBool b
    | STupleLit(el) ->  
        let env, args = List.fold_right (fun e (env, args) ->
          let env, arg = eval_expr env e in (env, arg :: args))
             el (env, []) in env, VTuple args
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
    | SUnop(op, ((Qubit, _) as e)) ->
        let env, q = unwrap_qubit (eval_expr env e) in
        (env, match op with
            Not -> print_string ("x " ^ q ^ "[0];\n"); VQubit(q)
          | _ -> raise (Failure "bad op")
        )
    | SUnop(_, _) -> raise (Failure "sounds like trouble")
    | SAssign(name, e) ->
        let env, e' = eval_expr env e in
        { env with name_map = StringMap.add name e' env.name_map }, e'
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
          | "hadamard", [VQubit q] ->
                  print_string ("h " ^ q ^ ";\n"); env, VQubit q
          | _ -> eval_func name args { env with counter = env.counter + 1 })
    | SNoexpr -> env, VNoexpr
    | _ -> let env, lval = eval_lval env (typ, expr) in
        let value = load_lval env lval in
        match value with
            VQubitInvalid(var) ->
              raise (Failure 
                ("qubit " ^ (string_of_lval var) ^ " used more than once"))
          | _ ->
            (if typ = Qubit then store_lval env (VQubitInvalid lval) lval else env),
            value

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

  eval_func name args env =
    let func = StringMap.find name function_map in
    let env = List.fold_left2 (fun env (_, name) arg ->
      { env with name_map = StringMap.add name arg env.name_map })
    env func.sformals args in
    let env = List.fold_left (fun env (typ, name) ->
      { env with name_map =
        StringMap.add name (default_val name env typ) env.name_map })
      env func.slocals in
    let _, sv = eval_stmt env func.sbody in
    (env, match sv with
        VNone -> VNoexpr
      | VReturn v -> v)
  in

  (* Temporary minimal circuit for testing *)
  print_string "OPENQASM 2.0;\n";
  print_string "include \"qelib1.inc\";\n";
  print_string "qreg q[1];\n";
  print_string "creg c[1];\n";
  print_string "h q;\n";

  let initial_env = { name_map = StringMap.empty; counter = 0; } in

  ignore (eval_func "main" [] initial_env)
