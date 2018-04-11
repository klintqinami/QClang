(* Top-level of the MicroC compiler: scan & parse the input,
   check the resulting AST, generate QASM, and dump the module *)

type action = Ast | Compile

let _ =
  let action = ref Compile in
  let input = ref "" in
  let set_action a () = action := a in
  let speclist = [
    ("-a", Arg.Unit (set_action Ast), "Print the SAST");
    ("-l", Arg.Unit (set_action Compile), "Print the generated QASM (default)");
  ] in
  let usage_msg = "usage: ./microc.native [-a|-l] [file]" in
  Arg.parse speclist (fun s -> input := s) usage_msg;
  let channel = if !input = "" then
    stdin
  else
    open_in !input
  in
  let lexbuf = Lexing.from_channel channel in
  let ast = Parser.program Scanner.token lexbuf in
  Semant.check ast;
  match !action with
    Ast -> print_string (Ast.string_of_program ast)
  | Compile -> Codegen.translate ast
