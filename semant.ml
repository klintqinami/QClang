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
     { typ = Qubit; fname = "U";        formals = [(Float, "x"); (Float, "y"); 
                                                   (Float, "z"); (Qubit, "x")]; 
       locals = []; body = [] };
     { typ = Tuple([Qubit; Qubit]); fname = "CX";
       formals = [(Qubit, "control"); (Qubit, "target")];
       locals = []; body = []; };
     { typ = Bit;   fname = "measure";  formals = [(Qubit, "x")];
       locals = []; body = [] };
     { typ = Int;   fname = "length"; formals = [(Int, "arr")]; (* dummy *)
       locals = []; body = []; };
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
  let rec check_assign lvaluet rvaluet err =
      (match lvaluet, rvaluet with
        Qubit, Bool -> lvaluet
      | Qubit, Bit  -> lvaluet
      | Tuple(ltyps), Tuple(rtyps) ->
          if List.length ltyps != List.length rtyps then
            raise (Failure err)
          else
            Tuple(List.map2 (fun ltyp rtyp ->
              check_assign ltyp rtyp err) ltyps rtyps)
      | Array(ltyp), Array(rtyp) ->
          Array(check_assign ltyp rtyp err)
      | _, _ -> if lvaluet = rvaluet then lvaluet else raise (Failure err))
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

    let check_const_int = function
        Literal i -> i
      | _ as e ->
          raise (Failure
            ("expected literal integer, but found " ^ (string_of_expr e)))
    in

    (* Return a semantically-checked expression, i.e., with a type *)
    let rec lexpr required = function
        Id s       -> (type_of_identifier s, SId s)
      | Deref(l, r) as e ->
          let (lt, _) as l' = lexpr required l and
              (rt, _) as r' = expr r in
          if rt != Int then raise
            (Failure ("index of " ^ (string_of_expr e) ^ "is not an integer"))
          else
            ((match lt with
                Tuple(typs) ->
                  let idx = check_const_int r in
                  if idx < 0 || idx >= List.length typs then
                    raise (Failure ("index " ^ (string_of_int idx) ^
                    " out of bounds in " ^ (string_of_expr e)))
                  else List.nth typs idx
              | Array(typ) -> typ
              | _ -> raise (Failure
                  ("cannot dereference " ^ (string_of_typ lt) ^ " in " ^
                  (string_of_expr e)))),
              SDeref(l', r'))
      | TupleLit(el) -> 
          let el' = List.map (fun e -> lexpr required e) el in
          let types = List.map fst el' in
          (Tuple(types), STupleLit(el'))
      | _ as e -> if required then
            raise (Failure ((string_of_expr e) ^ " is not an lvalue"))
          else
            expr e
    and expr = function
        Literal  l -> (Int, SLiteral l)
      | Fliteral l -> (Float, SFliteral l)
      | BoolLit l  -> (Bool, SBoolLit l)
      | TupleLit(el) -> 
          let el' = List.map expr el in
          let types = List.map (fun (t, _) -> t) el' in
          (Tuple(types), STupleLit(el'))
      | Noexpr     -> (Void, SNoexpr)
      | Assign(var, e) as ex -> 
          let (lt, _) as var' = lexpr true var
          and (rt, _) as e' = expr e in
          let err = "illegal assignment " ^ string_of_typ lt ^ " = " ^ 
            string_of_typ rt ^ " in " ^ string_of_expr ex
          in (check_assign lt rt err, SAssign(var', e'))
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
            | _ -> raise (Failure ("illegal binary operator " ^
                   string_of_typ t1 ^ " " ^ string_of_op op ^ " " ^
                   string_of_typ t2 ^ " in " ^ string_of_expr e))
          in (ty, SBinop((t1, e1'), op, (t2, e2')))
      | TypeCons(typ, args) as cons ->
          let args' = List.map expr args in
          (match typ, args' with
              Array(_), [(Int, _)] -> ()
            | _ -> raise (Failure
                ("invalid arguments to type constructor in " ^ (string_of_expr
                cons))));
          (typ, STypeCons(typ, args'))
      | Call(fname, args) as call -> 
          let fd = find_func fname in
          let param_length = List.length fd.formals in
          if List.length args != param_length then
            raise (Failure ("expecting " ^ string_of_int param_length ^ 
                        " arguments in " ^ string_of_expr call))

          else
            let check_call (args, vectorized) (ft, _) e = 
              let (et, e') = expr e in 
              let err = "illegal argument found " ^ string_of_typ et ^
                " expected " ^ string_of_typ ft ^ " in " ^ string_of_expr e
              in
              if et = Array(Qubit) && ft = Qubit then
                ((Array(Qubit), e') :: args, true)
              else if fname = "length" then
                match et with
                    Array(_) -> ([(et, e')], false)
                  | _ ->
                    raise (Failure ("array expected in call to length, got " ^
                    string_of_expr e))
              else
                ((check_assign ft et err, e') :: args, vectorized)
            in 
            let args', vectorized =
              List.fold_left2 check_call ([], false) fd.formals args in
            let args' = List.rev args'
            in ((if vectorized then Array(fd.typ) else fd.typ), SCall(fname, args'))
      | _ as e -> lexpr false e
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
    in

    let vectorize func = 
      let counter = ref 0 in
      let temps = ref ([] : (typ * String.t) list) in

      let vectorize_call func args dest =
        let index = "@tmpidx" ^ string_of_int !counter in
        counter := !counter + 1;
        temps := (Int, index) :: !temps;
        (* find an example of one thing that needs to be vectorized, to compute
         * the number of iterations of the for loop and the size of the output
         * array.
         *)
        let arr = List.fold_left2 (fun arr ((argtyp, _) as arg) (ftyp, _) ->
          if ftyp = Qubit && argtyp = Array(Qubit) then
            Some arg
          else
            arr) None args func.formals in
        let arr = match arr with
            Some a -> a
          | None ->
              raise (Failure "internal error foo")
        in
        SBlock([
          (* dest = qubit[](length(arr)); *)
          SExpr(Array(func.typ),
                SAssign((Array(func.typ), SId(dest)),
                        (Array(func.typ),
                         STypeCons(Array(func.typ),
                                   [(Int, SCall("length", [arr]))]))));
          (* for (index = 0; index < length(arr); index++) *)
          SFor((Int, SAssign((Int, SId(index)), (Int, SLiteral 0))),
               (Bool, SBinop((Int, SId(index)), Less,
                  (Int, SCall("length", [arr])))),
               (Int, SAssign((Int, SId(index)),
                  (Int, SBinop((Int, SId(index)), Add, (Int, SLiteral(1)))))),
               (* loop body: dest[index] = func(...); *)
               SExpr(func.typ, 
                SAssign((func.typ, SDeref((Array(func.typ), SId(dest)),
                                          (Int, SId(index)))),
                        (func.typ, SCall(func.fname,
                          List.map2 (fun (ftyp, _) ((argtyp, _) as e) ->
                            if ftyp = Qubit && argtyp == Array(Qubit) then
                              (Qubit, SDeref(e, (Int, SId(index))))
                            else
                              e) func.formals args)))))])
      in

      let rec flatten_call (typ, e) = match e with
          SCall(name, args) ->
            let args', stmts = List.split (List.map flatten_call args) in
            let stmts = List.flatten stmts in
            let tmp = "@tmp" ^ string_of_int !counter in
            counter := !counter + 1;
            temps := (typ, tmp) :: !temps;
            let func = find_func name in
            let need_vectorize = typ != func.typ in
            let stmt = if need_vectorize then
              vectorize_call func args tmp
            else
              (* @tmp = func(args) *)
              SExpr(typ, SAssign((typ, SId(tmp)), (typ, SCall(name, args'))))
            in
            ((typ, SId(tmp)), stmts @ [stmt])
        | STupleLit(el) ->
            let el', stmts = List.split (List.map flatten_call el) in
            let stmts = List.flatten stmts in
            ((typ, STupleLit(el')), stmts)
        | SBinop(e1, op, e2) ->
            let e1, stmt1 = flatten_call e1 in
            let e2, stmt2 = flatten_call e2 in
            ((typ, SBinop(e1, op, e2)), stmt1 @ stmt2)
        | SUnop(op, e) ->
            let e, stmts = flatten_call e in
            ((typ, SUnop(op, e)), stmts)
        | SAssign(lhs, rhs) ->
            let rhs, rstmts = flatten_call rhs in
            let lhs, lstmts = flatten_call lhs in
            (rhs, rstmts @ lstmts @ [SExpr(typ, (SAssign(lhs, rhs)))])
        | SDeref(lhs, rhs) ->
            let rhs, rstmts = flatten_call rhs in
            let lhs, lstmts = flatten_call lhs in
            ((typ, SDeref(lhs, rhs)), lstmts @ rstmts)
        | STypeCons(typ', el) ->
            let el', stmts = List.split (List.map flatten_call el) in
            let stmts = List.flatten stmts in
            ((typ, STypeCons(typ', el')), stmts)
        | _ as e -> ((typ, e), [])
      in

      let rec flatten_stmt = function
          SExpr e -> SBlock (snd (flatten_call e))
        | SBlock el -> SBlock (List.map flatten_stmt el)
        | SIf(p, b1, b2) -> SIf(p, flatten_stmt b1, flatten_stmt b2)
        | SFor(e1, e2, e3, st) -> SFor(e1, e2, e3, flatten_stmt st)
        | SWhile(p, s) -> SWhile(p, flatten_stmt s)
        | SReturn e -> let e, stmts = flatten_call e in
            SBlock(stmts @ [SReturn(e)])
      in
      { func with sbody = flatten_stmt func.sbody;
        slocals = !temps @ func.slocals }

    in (* body of check_function *)
    let sbody = check_stmt (Block func.body)
    in
    let sfunc = { styp = func.typ;
      sfname = func.fname;
      sformals = formals';
      slocals  = locals';
      sbody = sbody;
     } 
    in vectorize sfunc
  in List.map check_function functions
