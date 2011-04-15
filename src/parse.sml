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
    val es = []
    val ops = []
    (* parse_tokens lexer es ops is the AST for the expression defined
    * by the contents of es and ops together with the remaining tokens
    * yielded by lexer up to the first Tokens.EOS token, where es is 
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
  in
    parse_tokens lexer es ops
  end
  
  (* parse_program lexer is the AST.pgm for the program defined by the tokens
  *  yielded by lexer up to the Tokens.EOF token.
  *)

end
