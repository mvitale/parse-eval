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

  (* parse_expression lexer is the AST for the expression defined by the
  *  tokens yielded by lexer up to the first Tokens.EOS token.
  *)
  fun parse_expression lexer =
  let
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
        T.Ident(id) => parse_tokens lexer Ast.Ident(id)::es ops
        | T.Num(x)) => parse_tokens lexer Ast.Number(x)::es ops
        | (T.Unop(op) | T.Binop(op)) => 
            let
              val stacks = force_ops op es ops 
            in
              case stacks of
                (es', ops') => parse_tokens lexer es' op::ops'
            end
        | T.EOL => finish es ops
    end

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
  in
    parse_tokens lexer es ops
  end
  
  (* parse_program lexer is the AST.pgm for the program defined by the tokens
  *  yielded by lexer up to the Tokens.EOF token.
  *)

end
