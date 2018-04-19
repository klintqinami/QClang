(* Semantic checking for the QClang compiler *)

open Ast
open Sast

module StringMap = Map.Make(String)
module StringSet = Set.Make(String)

(* Semantic checking of the AST. Returns an SAST if successful,
   throws an exception if something is wrong.

   Check each function *)

let check functions =

  (* Check if a certain kind of binding has void type or is a duplicate
     of another, previously checked binding *)
  let check_binds (kind : string) (to_check : bind list) = 
    let check_it checked binding = 
      let void_err = "illegal void " ^ kind ^ " " ^ snd binding
      and dup_err = "duplicate " ^ kind ^ " " ^ snd binding
      in match binding with
        (* No void bindings *)
        (Void, _) -> raise (Failure void_err)
      | (_, n1) -> match checked with
                    (* No duplicate bindings *)
                      ((_, n2) :: _) when n1 = n2 -> raise (Failure dup_err)
                    | _ -> binding :: checked
    in let _ = List.fold_left check_it [] (List.sort compare to_check) 
       in to_check
  in 


  (* Collect function declarations for built-in functions *)
  let built_in_decls =
    [
     { typ = Void;  fname = "print";    formals = [(Int, "x")];
       locals = []; body = [] };
     { typ = Void;  fname = "printb";   formals = [(Bool, "x")];
       locals = []; body = [] };
     { typ = Void;  fname = "printf";   formals = [(Float, "x")];
       locals = []; body = [] };
     { typ = Qubit; fname = "hadamard"; formals = [(Qubit, "x")];
       locals = []; body = [] };
     { typ = Bit;   fname = "measure";  formals = [(Qubit, "x")];
       locals = []; body = [] };
    ]
  in


  (* Add function name to symbol table *)
  List.iter (fun built_in_decl ->
      let name = built_in_decl.fname in
      if List.mem name (List.map (fun fd -> fd.fname) functions)
      then raise (Failure ("function " ^ name ^ " may not be defined")) else ())
  built_in_decls;

  let function_decls = List.fold_left (fun m fd -> StringMap.add fd.fname fd m)
    StringMap.empty (built_in_decls @ functions)
  in

  (* Raise an exception if the given list has a duplicate *)
  let report_duplicate exceptf list =
    let rec helper = function
	n1 :: n2 :: _ when n1 = n2 -> raise (Failure (exceptf n1))
      | _ :: t -> helper t
      | [] -> ()
    in helper (List.sort compare list)
  in
  
  report_duplicate (fun n -> "duplicate function " ^ n)
    (List.map (fun fd -> fd.fname) functions);

  (* Return a function from our symbol table *)
  let find_func s = 
      try StringMap.find s function_decls
    with Not_found -> raise (Failure ("unrecognized function " ^ s))
  in

  let _ = find_func "main" in (* Ensure "main" is defined *)

  let check_function func =
      (* Make sure no formals or locals are void or duplicates *)
      let formals' = check_binds "formal" func.formals in
      let locals' = check_binds "local" func.locals in

      (* Raise an exception if the given rvalue type cannot be assigned to
       the given lvalue type *)
  let check_assign lvaluet rvaluet err =
      if lvaluet = rvaluet then lvaluet else raise (Failure err)
      in   

    (* Build local symbol table of variables for this function *)
    let symbols = List.fold_left (fun m (ty, name) -> StringMap.add name ty m)
    StringMap.empty (formals' @ locals')
  in

    (* Return a variable from our local symbol table *)
    let type_of_identifier s =
        try StringMap.find s symbols
      with Not_found -> raise (Failure ("undeclared identifier " ^ s))
    in


    (* Return a semantically-checked expression, i.e., with a type *)
    let rec expr = function
        Literal  l -> (Int, SLiteral l)
      | Fliteral l -> (Float, SFliteral l)
      | BoolLit l  -> (Bool, SBoolLit l)
      | TupleLit(el) -> 
          let el' = List.map expr el in
          let types = List.map (fun (t, _) -> t) el' in
          (Tuple(types), STupleLit(el'))
      | Noexpr     -> (Void, SNoexpr)
      | Id s       -> (type_of_identifier s, SId s)
      | Assign(var, e) as ex -> 
          let lt = type_of_identifier var
          and (rt, e') = expr e in
          let err = "illegal assignment " ^ string_of_typ lt ^ " = " ^ 
            string_of_typ rt ^ " in " ^ string_of_expr ex
          in (check_assign lt rt err, SAssign(var, (rt, e')))
      | Unop(op, e) as ex -> 
          let (t, e') = expr e in
          let ty = match op with
            Neg when t = Int || t = Float -> t
      | Not when t = Bool -> Bool
          | Not when t = Qubit -> Qubit
          | _ -> raise (Failure ("illegal unary operator " ^ 
                                 string_of_uop op ^ string_of_typ t ^
                                 " in " ^ string_of_expr ex))
          in (ty, SUnop(op, (t, e')))
          | Binop(e1, op, e2) as e -> 
              let (t1, e1') = expr e1 
          and (t2, e2') = expr e2 in
              (* All binary operators require operands of the same type *)
              let same = t1 = t2 in
              (* Determine expression type based on operator and operand types *)
              let ty = match op with
            Add | Sub | Mult | Div when same && t1 = Int   -> Int
          | Add | Sub | Mult | Div when same && t1 = Float -> Float
          | Equal | Neq            when same               -> Bool
          | Less | Leq | Greater | Geq
                     when same && (t1 = Int || t1 = Float) -> Bool
          | And | Or when same && t1 = Bool -> Bool
          | _ -> raise (
            Failure ("illegal binary operator " ^
                       string_of_typ t1 ^ " " ^ string_of_op op ^ " " ^
                       string_of_typ t2 ^ " in " ^ string_of_expr e))
              in (ty, SBinop((t1, e1'), op, (t2, e2')))
          | Call(fname, args) as call -> 
              let fd = find_func fname in
              let param_length = List.length fd.formals in
              if List.length args != param_length then
                raise (Failure ("expecting " ^ string_of_int param_length ^ 
                            " arguments in " ^ string_of_expr call))
      else let check_call (ft, _) e = 
        let (et, e') = expr e in 
        let err = "illegal argument found " ^ string_of_typ et ^
              " expected " ^ string_of_typ ft ^ " in " ^ string_of_expr e
        in (check_assign ft et err, e')
        in 
          let args' = List.map2 check_call fd.formals args
          in (fd.typ, SCall(fname, args'))
          in

    let check_bool_expr e = 
      let (t', e') = expr e
      and err = "expected Boolean expression in " ^ string_of_expr e
      in if t' != Bool then raise (Failure err) else (t', e') 
      in

    (* Return a semantically-checked statement i.e. containing sexprs *)
    let rec check_stmt = function
      Expr e -> SExpr(expr e)
          | If(p, b1, b2) ->
              SIf(check_bool_expr p, check_stmt b1, check_stmt b2)
          | For(e1, e2, e3, st) ->
              SFor(expr e1, check_bool_expr e2, expr e3, check_stmt st)
          | While(p, s) ->
              SWhile(check_bool_expr p, check_stmt s)
          | Return e -> let (t, e') = expr e in
          if t = func.typ then SReturn (t, e') 
          else raise (
            Failure ("return gives " ^ string_of_typ t ^ " expected " ^
           string_of_typ func.typ ^ " in " ^ string_of_expr e))

          (* A block is correct if each statement is correct and nothing
           follows any Return statement.  Nested blocks are flattened. *)
          | Block sl -> 
              let rec check_stmt_list = function
                [Return _ as s] -> [check_stmt s]
          | Return _ :: _   -> raise (Failure "nothing may follow a return")
          | Block sl :: ss  -> check_stmt_list (sl @ ss) (* Flatten blocks *)
            | s :: ss         -> check_stmt s :: check_stmt_list ss
            | []              -> []
    in SBlock(check_stmt_list sl)

              in (* body of check_function *)
    let sbody = check_stmt (Block func.body)
    in
    { styp = func.typ;
      sfname = func.fname;
      sformals = formals';
      slocals  = locals';
      sbody = sbody;
     }
    in List.map check_function functions
