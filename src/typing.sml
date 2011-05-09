structure Typing =
struct

  (* Raised by infer if the expression cannot be typed. *)
  exception infer_error of string

  (* Raised when an environment is applied to an identifier not in its 
  * domain.
  *)
  exception env_error

  type ident = string

  (* The type of type variables. *)
  type var = int

  (* The type of types. *)
  datatype t = V of var | Int | Bool | Arrow of t*t | List of t

  (* The type of our representation of formal type equations. *)
  type t_eq = t*t

  (* The type of labeled ast nodes. *)
  datatype l_expr = Ident of ident*t | Number of int*t | Boolean of bool*t |
                    UnOp of Ast.unop*l_expr*t | 
                    BinOp of Ast.binop*l_expr*l_expr*t | NilList of t |
                    Cond of l_expr*l_expr*l_expr*t | 
                    Abs of ident*t*l_expr*t |
                    App of l_expr*l_expr*t

  (* label_ast e is the l_ast corresponding to Ast.expr e labeled with type 
  * variables.
  * *)
  fun label_ast e =
  let
    (* The empty environment. *)
    fun empty_env x = raise env_error

    (* update_env e id v is the environment mapping x to v and everything
    *  else to its value under e.
    *)
    fun update_env env id v = fn x => if x = id then v else env id

    (* label_ast' e env fresh abs
    *
    * label_ast' e env fresh false is the l_ast corresponding to labeling
    * e with type variables. Identifiers with mappings under environment env 
    * will 
    * be assigned their vals under env, and everything else will be assigned a
    * new var >= fresh. If new identifiers are encountered, the same identifier
    * will always be assigned the same var. 
    *
    * label_ast' e env fresh true is the l_ast corresponding to labeling
    * e with type variables. Identifiers with mappings under environment env
    * will be assigned their vals under env. If new identifiers (identifiers
    * not bound under env) are encountered, an infer_error will be raised. We
    * need to raise an error at this stage if this occurs, because otherwise it
    * is possible that the e will pass all of type inference and pass to
    * evaluation with unbound variables. Consider the expression
    * fn x => z. If we don't raise an error when we encounter z, type inference
    * will pass, and evaluation will as well, since this expression will simply 
    * evaluate to itself and z will never be examined during evaluation.
    *
    * abs should be set to true when making recursive calls inside of an 
    * abstraction, and false o/w.
    *)
    fun label_ast' (Ast.Ident(x)) env fresh abs =
        let
          val tx = env x handle env_error => 
            if abs then raise infer_error "Unbound identifier." else fresh
          val is_fresh = tx = fresh
        in
          (Ident(x, V tx), if is_fresh then update_env env x fresh else env,
           if is_fresh then fresh+1 else fresh)
        end
      | label_ast' (Ast.Number(n)) env fresh abs =
          (Number(n, V fresh), env, fresh+1)
      | label_ast' (Ast.Boolean(b)) env fresh abs =
          (Boolean(b, V fresh), env, fresh+1)
      | label_ast' (Ast.UnOp(opr, e)) env fresh abs =
        let
          val e' = label_ast' e env (fresh+1) abs
        in
          (UnOp(opr, #1 e'), #2 e', #3 e')
      | label_ast' (Ast.BinOp(opr, e1, e2)) env fresh abs =
        let
          val e1' = label_ast' e1 env (fresh+1) abs
          val e2' = label_ast' e2 (#2 e1') (#3 e1') abs
        in
          (BinOp(opr, #1 e1', #1 e2', fresh), #2 e2', #3 e2')
        end
      | label_ast' Ast.NilList env fresh abs =
          (NilList fresh, env, fresh+1)
      | label_ast' (Ast.Cond(e1, e2, e3)) env fresh abs =
        let
          val e1' = label_ast' e1 env (fresh+1) abs
          val e2' = label_ast' e2 (#2 e1') (#3 e1') abs
          val e3' = label_ast' e3 (#2 e2') (#3 e2') abs
        in
          (Cond(#1 e1', #1 e2', #1 e3', fresh), #2 e3', #3 e3')
        end
      | label_ast' (Ast.Abs(x, e)) env fresh abs =
        let
          val env' = update_env env x (fresh+1)
          val e' = label_ast' e env' (fresh+2) true
        in
          (Abs(x, fresh+1, #1 e', fresh), env, #3 e')
        end
      | label_ast' (Ast.App(e1, e2)) env fresh abs =
        let
          val e1' = label_ast' e1 env (fresh+1) abs
          val e2' = label_ast' e2 (#2 e1') (#3 e1') abs
        in
          (App(#1 e1', #1 e2', fresh), #2 e2', #3 e2')
        end

    val result = 
  in
    case label_ast' e empty_env 0 false of
         (expr, env, fresh) => (expr, fresh)
  end

  (* get_type e is the t with which l_expr is labeled. *)
  fun get_type Ident(_, t) = t
    | get_type Number(_, t) = t
    | get_type Boolean(_, t) = t
    | get_type UnOp(_, _, t) = t
    | get_type BinOp(_, _, _, t) = t
    | get_type NilList(t) = t
    | get_type Cond(_, _, _, t) = t
    | get_type Abs(_, _, _, t) = t
    | get_type App(_, _, t) = t

  (* infer e => the most general type of e, inferred using Hindley-Milner.
  *  Raises infer_error if no type can be inferred for e.
  *)

  (* toString s => a fully-parenthesized string representation of the
  *  type s.
  *)
end
