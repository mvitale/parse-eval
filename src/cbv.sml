(* Michael Vitale
*
* Implementation of the EVAL signature.
*)
structure L1Cbv =
struct

  (* The type of the value returned by the evaluation functions. *)
  datatype value = Number of int | Boolean of bool | Abs of Ast.ident * Ast.expr

  (* eval_expr e is the value to which the expression e evaluates. *)
  fun eval_expr (Ast.Number(num)) = Number num
    | eval_expr (Ast.Boolean(b)) = Boolean b
    | eval_expr (Ast.Abs(id, e)) = Abs (id, e)
    | eval_expr (Ast.UnOp(opr, e)) =
      let
        val e' = eval_expr e
      in
        case opr of
               Ast.NEG => 
                (case e' of (Number num) => Number (~num))
             | Ast.NOT => 
                (case e' of (Boolean boolean) => Boolean (not boolean))
                               
      end
    | eval_expr (Ast.BinOp(opr, e1, e2)) =
      let
        val e1' = eval_expr e1
        val e2' = eval_expr e2
      in
        case opr of
               Ast.SUB => 
                (case e1' of (Number num1) => case e2' of (Number num2) => 
                Number (num1 - num2))
             | Ast.PLUS => 
                (case e1' of Number num1 => case e2' of Number num2 => 
                Number (num1 + num2))
             | Ast.TIMES => 
                (case e1' of Number num1 => case e2' of Number num2 => 
                Number (num1 * num2))
             | Ast.DIV => 
                (case e1' of Number num1 => case e2' of Number num2 => 
                Number (num1 div num2))
             | Ast.LT =>
                (case e1' of Number num1 => case e2' of Number num2 => 
                Boolean (num1 < num2))
             | Ast.LE =>
                (case e1' of Number num1 => case e2' of Number num2 => 
                Boolean (num1 <= num2))
             | Ast.GT =>
                (case e1' of Number num1 => case e2' of Number num2 => 
                Boolean (num1 > num2))
             | Ast.GE =>
                (case e1' of Number num1 => case e2' of Number num2 => 
                Boolean (num1 >= num2))
             | Ast.EQ =>
                (case e1' of Number num1 => case e2' of Number num2 => 
                Boolean (num1 = num2))
             | Ast.NE =>
                (case e1' of Number num1 => case e2' of Number num2 => 
                Boolean (num1 <> num2))
             | Ast.AND =>
                (case e1' of Boolean bool1 => case e2' of Boolean bool2 =>
                Boolean (bool1 andalso bool2))
             | Ast.OR =>
                (case e1' of Boolean bool1 => case e2' of Boolean bool2 =>
                Boolean (bool1 orelse bool2))
      end
    | eval_expr (Ast.Cond(e1, e2, e3)) =
      let
        val e1' = eval_expr e1
      in
        case e1' of
             Boolean(true) => eval_expr e2
           | Boolean(false) => eval_expr e3
      end
  


  (* eval_pgm p is the value to which the program p evaluates. *)
  (* UNIMPLEMENTED *)
  fun eval_pgm p = Number 1

  (* value2ast v is the AST corresponding to the value v. *)
  fun value2ast (Boolean boolean) = Ast.Boolean boolean
    | value2ast (Number num) = Ast.Number num
    | value2ast (Abs (id, e)) = Ast.Abs(id, e)
end
