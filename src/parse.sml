(* Michael Vitale
 * CS 321
 * HW 9
 * 
 * An implementation of the PARSE signature.
 *)

structure L1Parse =
struct
  
  (* Raised when an error occurs during parsing. *)
  exception parse_error of string

  (* A shorter name for Tokens. *)
  structure T = Tokens

  (* A datatype to represent FINISH pseudo-operator with higher precedence
  * than any other operator.
  *)
  datatype finish = FINISH

  (* parse_expression lexer is the AST for the expression defined by the
  *  tokens yielded by lexer up to the first Tokens.EOS token.
  *)
  fun parse_expression lexer =
  let

    (* prec op = the precedence of operator op, i.e., an int such that
    * if op1 has greater precedence than op2, (prec op1 > prec op2.
    *)
    fun prec (Ast.PLUS | Ast.SUB) = 1
      | prec (Ast.TIMES | Ast.DIV) = 2
      | prec Ast.NEG = 3
      | prec FINISH = 100


    (* force_op es ops = (es', ops') where es' and ops' are the new expression
    * and operation stacks resulting from forcing the top operation of ops.
    *)
    fun force_op (e::es) (T.Unop(op)::ops) = 
          ((Ast.UnOp(op, e)::es), ops)
      | force_op (right::left::es) (T.Binop(op)::ops) = 
          ((Ast.BinOp(op, left, right)::es), ops)

    (* force_ops op es ops = (es', ops') where es' and ops' are the new
    * expression and operation stacks resulting from forcing all operations
    * on ops of greater precedence than op.
    *)
    fun force_ops _ es [] = (es, [])
      | force_ops op es (op'::ops) =
          if prec(op) < prec(op') then
            let
              val stacks = force_op es (op'::ops)
              val es' = #1 stacks
              val ops' = #2 stacks
            in
              force_ops op es' ops'
            end
          else
            (es, (op'::ops))

    (* force_all_ops es ops = the Ast representing the result of forcing all
    * operations on ops.
    *)
    fun force_all_ops es ops =
    let
      val es' = #1(force_ops FINISH es ops)
    in
      hd es'
    end

    (* parse_tokens lexer es ops is the AST for the expression defined
    * by the contents of es and ops together with the remaining tokens
    * yielded by lexer up to the first Tokens.EOL token, where es is 
    * the expression stack and ops is the operation stack.
    *)
    fun parse_tokens lexer es ops =
    let
      val tok = lexer()
    in
      case tok of
        T.Ident(id) = parse_tokens lexer (Ast.Ident(id)::es) ops
        | T.Num(num) = parse_tokens lexer (Ast.Number(num)::es) ops
        | (T.Unop(op) | T.Binop(op)) = 
          let
            val stacks = force_ops tok es ops
          in
            case stacks of
              (es', ops') => parse_tokens lexer es' (tok::ops')
          end
    end
  in
    parse_tokens lexer [] []
  end
  
  (* parse_program lexer is the AST.pgm for the program defined by the tokens
  *  yielded by lexer up to the Tokens.EOF token.
  *)

end
