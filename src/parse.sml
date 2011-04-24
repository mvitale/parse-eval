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

  (* The type of the elements of the operation stack. Defining a new type
  * altogether makes for cleaner code than creating a disjoint sum of Tokens.t 
  * and ILParen. In addition, many of the tokens should never be pushed onto
  * the operation stack; using a separate datatype enforces this.
  *)
  datatype o = Unop of Ast.unop | Binop of Ast.binop | Lambda of T.ident |
               RParen | LParen | ILParen 

  (* The type of the elements of the expression stack. In this case,
  * each element should either be an AST representing an expression or
  * the BGroup identifier. So, we define this type to be the disjoint
  * sum of Ast.expr and BGroup.
  *)
  datatype e = Exp of Ast.expr | BGroup

  (* parse_expression lexer is the AST for the expression defined by the
  *  tokens yielded by lexer up to the first Tokens.EOS token.
  *)
  fun parse_expression lexer =
  let

    (* prec op = the precedence of operator op, i.e., an int such that
    * if op1 has greater precedence than op2, prec op1 > prec op2.
    *)
    fun prec (Lambda _) = 1
      | prec (Binop(Ast.AND) | Binop(Ast.OR)) = 2
      | prec (Binop(Ast.LT) | Binop(Ast.LE) | Binop(Ast.GT) |
              Binop(Ast.GE) | Binop(Ast.EQ) | Binop(Ast.NE)) = 3
      | prec (Binop(Ast.PLUS) | Binop(Ast.SUB)) = 5
      | prec (Binop(Ast.TIMES) | Binop(Ast.DIV)) = 6
      | prec (Unop(Ast.NEG) | Unop(Ast.NOT)) = 8

    (* assoc op = LEFT if op is left-associative, RIGHT o/w. *)
    fun assoc (Binop(Ast.PLUS) | Binop(Ast.SUB) | Binop(Ast.TIMES) |
               Binop(Ast.DIV) | Binop(Ast.AND) | Binop(Ast.OR) |
               Binop(Ast.LT) | Binop(Ast.LE) | Binop(Ast.GT) |
               Binop(Ast.GE) | Binop(Ast.EQ) | Binop(Ast.NE)) = LEFT
      | assoc (Unop(Ast.NEG) | Unop(Ast.NOT) | Lambda _) = RIGHT

    (* force_op es ops = (es', ops') where es' and ops' are the new expression
    * and operation stacks resulting from forcing the top operation of ops.
    *)
    fun force_op ((Exp e)::es) ((Unop(opr))::ops) = 
          ((Exp(Ast.UnOp(opr, e)))::es, ops)
      | force_op ((Exp right)::(Exp left)::es) ((Binop(opr))::ops) = 
          ((Exp(Ast.BinOp(opr, left, right)))::es, ops)
      | force_op ((Exp e)::es) ((Lambda(id))::ops) =
          ((Exp(Ast.Abs(id, e)))::es, ops)

    (* collect_es ((Exp ek)::...::(Exp e1)::BGroup::es) =
    * ((Exp (Ast.App...(Ast.App(e1, e2), e3)..., ek))::BGroup::es)
    *)
    fun collect_es ((Exp e2)::(Exp e1)::BGroup::es) = 
          ((Exp(Ast.App(e1, e2)))::BGroup::es)
      | collect_es ((Exp e)::es) =
        let
          val es' = collect_es es
        in
          case es' of
               ((Exp app)::e') => ((Exp(Ast.App(app, e)))::e')
        end

    (* force_ops op es ops = (es', ops') where es' and ops' are the new
    * expression and operation stacks resulting from forcing all operations
    * on ops of lesser or equal precedence than op.
    *)
    fun force_ops _ es [] = (es, [])
      | force_ops opr es (LParen::ops) = 
        let
          val es' = collect_es es
        in
          case opr of
               RParen => (case es' of (BGroup::e) => (e, ops))
             | _ => (es', (LParen::ops))
        end
      | force_ops opr es (ILParen::ops) =
        let
          val es' = collect_es es
        in
          case es' of
               (BGroup::e) => force_ops opr e ops
        end
      | force_ops RParen es ops =
        let
          val stacks = force_op es ops
        in
          case stacks of
               (es', ops') => force_ops RParen es' ops'
        end
      | force_ops opr es (opr'::ops) =
        let
          val p = prec opr
          val p' = prec opr'
        in 
          if p < p' orelse (p = p' andalso assoc opr = LEFT) then
            let
              val stacks = force_op es (opr'::ops)
            in
              case stacks of
                (es', ops') => force_ops opr es' ops'
            end
          else
            (es, (opr'::ops))
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
        T.Ident(id) => parse_tokens lexer ((Exp(Ast.Ident(id)))::es) ops
        | T.Num(num) => parse_tokens lexer ((Exp(Ast.Number(num)))::es) ops
        | T.True => parse_tokens lexer ((Exp(Ast.Boolean(true)))::es) ops
        | T.False => parse_tokens lexer ((Exp(Ast.Boolean(false)))::es) ops
        | T.Unop(opr) =>
          let
            val stacks = force_ops (Unop opr) es ops
          in
            case stacks of
                 (es', ops') => parse_tokens lexer (BGroup::es')
                                (ILParen::(Unop(opr))::ops')
          end
        | T.Binop(opr) =>
          let
            val stacks = force_ops (Binop opr) es ops
          in
            case stacks of
                 (es', ops') => parse_tokens lexer (BGroup::es')
                                (ILParen::(Binop(opr))::ops')
          end
        | T.Lambda(id) =>
          let
            val stacks = force_ops (Lambda id) es ops
          in
            case stacks of
                 (es', ops') => parse_tokens lexer (BGroup::es')
                                (ILParen::(Lambda id)::ops')
          end
        | T.LParen => parse_tokens lexer (BGroup::es) (LParen::ops)
        | T.RParen => 
          let
            val stacks = force_ops RParen es ops
          in
            case stacks of
                 (es', ops') => parse_tokens lexer es' ops'
          end
        | T.If => parse_tokens lexer es (LParen::ops)
        | (T.Then | T.Else) =>
          let
            val stacks = force_ops RParen es ops
          in
            case stacks of
                 (es', ops') => parse_tokens lexer es' (LParen::ops')
          end
        | T.Endif =>
          let
            val stacks = force_ops RParen es ops
          in
            case stacks of
                 ((Exp e3)::(Exp e2)::(Exp e1)::es', ops') =>
                  parse_tokens lexer ((Exp(Ast.Cond(e1, e2, e3)))::es') ops'
          end
        | T.EOS => 
          let
            val e = hd (#1 (force_ops RParen es ops))
          in
            case e of
                 Exp(ast) => ast
          end
    end
  in
    parse_tokens lexer [] [LParen]
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
