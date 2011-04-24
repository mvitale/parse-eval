(* Michael Vitale
*
* Implementation of the EVAL signature.
*)
structure L1Cbv =
struct

  (* The type of a value expression. *)
  datatype value_exp = Number of int | Boolean of bool | Abs of Ast.ident * Ast.expr

  (* The type of the value returned by the evaluation functions. 
  *  SO FAR: A CLOSURE WHOSE EXPRESSION IS A VALUE EXPRESSION 
  *)
  datatype value = Closure of value_exp * (Ast.ident -> value)

  (* Raised when some errors occur during evaluation. *)
  exception eval_error of string

  (* The empty environment function. *)
  fun empty_env _ = raise eval_error
    "Tried to evaluate the value of an identifier under the empty environemnt."

  (* update_env env x v = env' where
  *  env' y = v if y=x, env y o/w.
  *)
  fun update_env env x v = fn y => if y = x then v else env y

  (* eval_expr e is the value to which the expression e evaluates. *)
  fun eval_expr e =
  let
    fun eval (Ast.Number(num)) _ = Closure(Number num, empty_env)
      | eval (Ast.Boolean(b)) _ = Closure(Boolean b, empty_env)
      | eval (Ast.Ident(id)) env = env id
      | eval (Ast.Abs(id, e)) env = Closure(Abs(id, e), env)
      | eval (Ast.UnOp(opr, e)) env =
        let
          val e' = eval e env
        in
          case opr of
               Ast.NEG =>
                 (case e' of Closure(Number num, env') => 
                   Closure(Number(~num), env'))
             | Ast.NOT =>
                 (case e' of Closure(Boolean b, env') =>
                  Closure(Boolean(not b), env'))
        end
      | eval (Ast.BinOp(opr, e1, e2)) env =
        let
          val e1' = eval e1 env
          val e2' = eval e2 env
        in
          case opr of
               Ast.SUB =>
                (case e1' of Closure(Number num1, _) => 
                 case e2' of Closure(Number num2, _) =>
                 Closure(Number(num1 - num2), empty_env))
             | Ast.PLUS =>
                (case e1' of Closure(Number num1, _) => 
                 case e2' of Closure(Number num2, _) =>
                 Closure(Number(num1 + num2), empty_env))
             | Ast.TIMES =>
                (case e1' of Closure(Number num1, _) => 
                 case e2' of Closure(Number num2, _) =>
                 Closure(Number(num1 * num2), empty_env))
             | Ast.DIV =>
                (case e1' of Closure(Number num1, _) => 
                 case e2' of Closure(Number num2, _) =>
                 Closure(Number(num1 div num2), empty_env))
             | Ast.LT =>
                 (case e1' of Closure(Number num1, _) =>
                  case e2' of Closure(Number num2, _) =>
                  Closure(Boolean(num1 < num2), empty_env))
             | Ast.LE =>
                 (case e1' of Closure(Number num1, _) =>
                  case e2' of Closure(Number num2, _) =>
                  Closure(Boolean(num1 <= num2), empty_env))
             | Ast.GT =>
                 (case e1' of Closure(Number num1, _) =>
                  case e2' of Closure(Number num2, _) =>
                  Closure(Boolean(num1 > num2), empty_env))
             | Ast.GE =>
                 (case e1' of Closure(Number num1, _) =>
                  case e2' of Closure(Number num2, _) =>
                  Closure(Boolean(num1 >= num2), empty_env))
             | Ast.EQ =>
                 (case e1' of Closure(Number num1, _) =>
                  case e2' of Closure(Number num2, _) =>
                  Closure(Boolean(num1 = num2), empty_env))
             | Ast.NE =>
                 (case e1' of Closure(Number num1, _) =>
                  case e2' of Closure(Number num2, _) =>
                  Closure(Boolean(num1 <> num2), empty_env))
             | Ast.AND =>
                (case e1' of Closure(Boolean b1, _) => 
                 case e2' of Closure(Boolean b2, _) =>
                 Closure(Boolean(b1 andalso b2), empty_env))
             | Ast.OR =>
                (case e1' of Closure(Boolean b1, _) => 
                 case e2' of Closure(Boolean b2, _) =>
                 Closure(Boolean(b1 orelse b2), empty_env))
        end
      | eval (Ast.Cond(e1, e2, e3)) env =
        let
          val e1' = eval e1 env
        in
          case e1' of
               Closure(Boolean true, _) => eval e2 env
             | Closure(Boolean false, _) => eval e3 env
        end
      | eval (Ast.App(e1, e2)) env =
        let
          val e1' = eval e1 env
          val e2' = eval e2 env
        in
          (case e1' of Closure(Abs(id, body), env1) =>
           let
             val new_env = update_env env1 id e2'
           in
             eval body new_env
           end)
        end
  in
    eval e empty_env
  end

  (* eval_pgm p is the value to which the program p evaluates. *)
  (* UNIMPLEMENTED *)
  fun eval_pgm p = Closure(Number 1, empty_env)

  (* value2ast v is the AST corresponding to the value v. *)
  fun value2ast (Closure(Boolean b, _)) = Ast.Boolean b
    | value2ast (Closure(Number num, _)) = Ast.Number num
    | value2ast (Closure(Abs(id, e), _)) = Ast.Abs(id, e)
end
