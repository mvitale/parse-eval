(* Michael Vitale
*
* Implementation of the EVAL signature.
*)
structure L1Cbv =
struct

  (* The type of the value returned by the evaluation functions. 
  *
  * XXX: This obviously needs to be changed, but define values to
  * be ints for now in order to implement evaluation of arithmatic
  * expressions.
  *)
  type value = int

  (* eval_expr e is the value to which the expression e evaluates. *)
  fun eval_expr (Ast.Number(num)) = num
    | eval_expr (Ast.UnOp(Ast.NEG, e)) = ~(eval_expr e)
    | eval_expr (Ast.BinOp(Ast.PLUS, e1, e2)) = (eval_expr e1) + (eval_expr e2)
    | eval_expr (Ast.BinOp(Ast.TIMES, e1, e2)) = (eval_expr e1) * (eval_expr e2)
    | eval_expr (Ast.BinOp(Ast.DIV, e1, e2)) = (eval_expr e1) div (eval_expr e2)

  (* Unimplemented functions *)

  (* eval_pgm p is the value to which the program p evaluates. *)
  fun eval_pgm p = 1

  (* values2ast v is the AST corresponding to the value v. *)
  fun values2ast v = Ast.NEG
end
