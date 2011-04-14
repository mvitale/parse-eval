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
   * tokens yielded by lexer up to the first Tokens.EOS token.
   *)
  
  (* parse_program lexer is the AST.pgm for the program defined by the tokens
  *  yielded by lexer up to the Tokens.EOF token.
  *)

end
