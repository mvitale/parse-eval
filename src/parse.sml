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

  (* An 'enumerated type' to represent left and right operator associativity.
  *)
  datatype lr = LEFT | RIGHT

  (* parse_expression lexer is the AST for the expression defined by the
  *  tokens yielded by lexer up to the first Tokens.EOS token.
  *)
  fun parse_expression lexer =
  let

    (* prec op = the precedence of operator op, i.e., an int such that
    * if op1 has greater precedence than op2, prec op1 > prec op2.
    *)
    fun prec (T.Binop(Ast.AND) | T.Binop(Ast.OR)) = 2
      | prec (T.Binop(Ast.LT) | T.Binop(Ast.LE) | T.Binop(Ast.GT) |
              T.Binop(Ast.GE) | T.Binop(Ast.EQ) | T.Binop(Ast.NE)) = 3
      | prec (T.Binop(Ast.PLUS) | T.Binop(Ast.SUB)) = 5
      | prec (T.Binop(Ast.TIMES) | T.Binop(Ast.DIV)) = 6
      | prec (T.Unop(Ast.NEG) | T.Unop(Ast.NOT)) = 8

    (* assoc op = LEFT if op is left-associative, RIGHT o/w. *)
    fun assoc ((T.Binop(Ast.PLUS)) | (T.Binop(Ast.SUB)) | (T.Binop(Ast.TIMES)) |
               (T.Binop(Ast.DIV)) | (T.Binop(Ast.AND)) | (T.Binop(Ast.OR))) = LEFT
      | assoc (T.Unop(Ast.NEG) | T.Unop(Ast.NOT)) = RIGHT

    (* force_op es ops = (es', ops') where es' and ops' are the new expression
    * and operation stacks resulting from forcing the top operation of ops.
    *)
    fun force_op (e::es) ((T.Unop(opr))::ops) = 
        (((Ast.UnOp(opr, e))::es), ops)
      | force_op (right::left::es) ((T.Binop(opr))::ops) = 
          ((Ast.BinOp(opr, left, right)::es), ops)

    (* force_ops op es ops = (es', ops') where es' and ops' are the new
    * expression and operation stacks resulting from forcing all operations
    * on ops of lesser or equal precedence than op.
    *)
    fun force_ops _ es [] = (es, [])
      | force_ops _ es (T.LParen::ops) = (es, (T.LParen::ops))
      | force_ops opr es (opr'::ops) =
        let
          val p = prec opr
          val p' = prec opr'
        in if p < p' orelse (p = p' andalso assoc opr = LEFT) then
            let
              val stacks = force_op es (opr'::ops)
            in
              case stacks of
                (es', ops') => force_ops opr es' ops'
            end
          else
            (es, (opr'::ops))
        end

    (* force_ops_to_lparen es ops = (es', ops') where es' and ops' are the
    * expression and operation stacks resulting from forcing all operations
    * on ops to the first Tokens.LParen and then popping the LParen from ops.
    *)
    fun force_ops_to_lparen es (T.LParen::ops) = (es, ops)
      | force_ops_to_lparen es ops =
        let
          val stacks = force_op es ops
        in
          case stacks of
            (es', ops') => force_ops_to_lparen es' ops'
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
        T.Ident(id) => parse_tokens lexer ((Ast.Ident(id))::es) ops
        | T.Num(num) => parse_tokens lexer ((Ast.Number(num))::es) ops
        | T.True => parse_tokens lexer ((Ast.Boolean(true))::es) ops
        | T.False => parse_tokens lexer ((Ast.Boolean(false))::es) ops
        | (T.Unop(_) | T.Binop(_)) => 
          let
            val stacks = force_ops tok es ops
          in
            case stacks of
              (es', ops') => parse_tokens lexer es' (tok::ops')
          end
        | T.LParen => parse_tokens lexer es (T.LParen::ops)
        | T.RParen => 
          let
            val stacks = force_ops_to_lparen es ops
          in
            case stacks of
              (es', ops') => parse_tokens lexer es' ops'
          end
        | T.EOS => hd (#1 (force_ops_to_lparen es ops))
    end
  in
    parse_tokens lexer [] [T.LParen]
  end
  
  (* parse_program lexer is the AST.pgm for the program defined by the tokens
  *  yielded by lexer up to the Tokens.EOF token.
  *)
  fun parse_program lexer =
  let
    (* parse_partial_program lexer stmts is the AST.pgm for the program
    * yielded by lexer up to the Tokens.EOF token along with the 
    * Ast.stmt's contained in stmts.
    *)
    fun parse_partial_program lexer stmts =
    let
      val tok = lexer()
    in
      case tok of
        T.Assign(id) =>
          let 
            val e = parse_expression lexer
            val s = Ast.Assign(id, e)
          in
            parse_partial_program lexer (s::stmts)
          end
        | T.EOF => Ast.Program(stmts)
    end
  in
    parse_partial_program lexer []
  end


end
