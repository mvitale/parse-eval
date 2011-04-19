(* Michael Vitale
*
* Implementation of the EVAL signature.
*)
structure L1Cbv =
struct

  (* The type of the value returned by the evaluation functions. *)
  datatype value = Num of int | Boolean of bool

  (* eval_expr e is the value to which the expression e evaluates. *)
  fun eval_expr (Ast.Number(num)) = Num num
    | eval_expr (Ast.Boolean(b)) = Boolean b
    | eval_expr (Ast.UnOp(opr, e)) =
      let
        val e' = eval_expr e
      in
        case opr of
               Ast.NEG => 
                (case e' of (Num num) => Num (~num))
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
                (case e1' of (Num num1) => case e2' of (Num num2) => 
                Num (num1 - num2))
             | Ast.PLUS => 
                (case e1' of Num num1 => case e2' of Num num2 => 
                Num (num1 + num2))
             | Ast.TIMES => 
                (case e1' of Num num1 => case e2' of Num num2 => 
                Num (num1 * num2))
             | Ast.DIV => 
                (case e1' of Num num1 => case e2' of Num num2 => 
                Num (num1 div num2))
             | Ast.LT =>
                (case e1' of Num num1 => case e2' of Num num2 => 
                Boolean (num1 < num2))
             | Ast.LE =>
                (case e1' of Num num1 => case e2' of Num num2 => 
                Boolean (num1 <= num2))
             | Ast.GT =>
                (case e1' of Num num1 => case e2' of Num num2 => 
                Boolean (num1 > num2))
             | Ast.GE =>
                (case e1' of Num num1 => case e2' of Num num2 => 
                Boolean (num1 >= num2))
             | Ast.EQ =>
                (case e1' of Num num1 => case e2' of Num num2 => 
                Boolean (num1 = num2))
             | Ast.NE =>
                (case e1' of Num num1 => case e2' of Num num2 => 
                Boolean (num1 <> num2))
             | Ast.AND =>
                (case e1' of Boolean bool1 => case e2' of Boolean bool2 =>
                Boolean (bool1 andalso bool2))
             | Ast.OR =>
                (case e1' of Boolean bool1 => case e2' of Boolean bool2 =>
                Boolean (bool1 orelse bool2))
      end


  (* eval_pgm p is the value to which the program p evaluates. *)
  (* UNIMPLEMENTED *)
  fun eval_pgm p = Num 1

  (* value2ast v is the AST corresponding to the value v. *)
  fun value2ast (Boolean boolean) = Ast.Boolean boolean
    | value2ast (Num num) = Ast.Number num
end
