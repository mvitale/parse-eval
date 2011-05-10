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

  (* Essentially an enumerated type to use as an extra component of our type
  * equations. For use with the unify' function. 
  *
  * This component should be
  * NEW if a substitution has never been generated from this equation, or
  * ACTIVE if a substitution has been generated from this equation and 
  *        still must be applied to other equations.
  * DONE if a substitution has been generated from this equation and has been
  *      applied to every other equation.
  *)
  datatype t_flag = NEW | ACTIVE | DONE

  (* The type of our representation of a formal type equation. The bool
  * component is used to represent whether or not a substitution has been
  * generated from the equation.*)
  datatype t_eq = Eq of t*t*t_flag

  (* The type of a single substitution. *)
  datatype s = Sub of var*t

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
          case opr of 
               Ast.TAIL => (UnOp(opr, #1 e', List(V fresh)), #2 e', #3 e')
             | _ => (UnOp(opr, #1 e', V fresh), #2 e', #3 e')
        end
      | label_ast' (Ast.BinOp(opr, e1, e2)) env fresh abs =
        let
          val e1' = label_ast' e1 env (fresh+1) abs
          val e2' = label_ast' e2 (#2 e1') (#3 e1') abs
        in
          case opr of
               Ast.CONS => 
               (BinOp(opr, #1 e1', #1 e2', List(V fresh)), #2 e2', #3 e2')
             | _ => (BinOp(opr, #1 e1', #1 e2', V fresh), #2 e2', #3 e2')
        end
      | label_ast' Ast.NilList env fresh abs =
          (NilList(List(V fresh)), env, fresh+1)
      | label_ast' (Ast.Cond(e1, e2, e3)) env fresh abs =
        let
          val e1' = label_ast' e1 env (fresh+1) abs
          val e2' = label_ast' e2 (#2 e1') (#3 e1') abs
          val e3' = label_ast' e3 (#2 e2') (#3 e2') abs
        in
          (Cond(#1 e1', #1 e2', #1 e3', V fresh), #2 e3', #3 e3')
        end
      | label_ast' (Ast.Abs(x, e)) env fresh abs =
        let
          val env' = update_env env x (fresh+1)
          val e' = label_ast' e env' (fresh+2) true
        in
          (Abs(x, V(fresh+1), #1 e', V fresh), env, #3 e')
        end
      | label_ast' (Ast.App(e1, e2)) env fresh abs =
        let
          val e1' = label_ast' e1 env (fresh+1) abs
          val e2' = label_ast' e2 (#2 e1') (#3 e1') abs
        in
          (App(#1 e1', #1 e2', V fresh), #2 e2', #3 e2')
        end
  in
    case label_ast' e empty_env 0 false of
         (expr, env, fresh) => (expr, fresh)
  end

  (* get_type e is the t with which l_expr is labeled. *)
  fun get_type (Ident(_, t)) = t
    | get_type (Number(_, t)) = t
    | get_type (Boolean(_, t)) = t
    | get_type (UnOp(_, _, t)) = t
    | get_type (BinOp(_, _, _, t)) = t
    | get_type (NilList(t)) = t
    | get_type (Cond(_, _, _, t)) = t
    | get_type (Abs(_, _, _, t)) = t
    | get_type (App(_, _, t)) = t

  (* gen_const e is a list of t_eq representing constraints generated
  * from the form of l_expr e.
  *)
  fun gen_const' (Ident(_, _) | NilList(_)) = []
    | gen_const' (Number(_, t)) = [Eq(t, Int, NEW)]
    | gen_const' (Boolean(_, t)) = [Eq(t, Bool, NEW)]
    | gen_const' (UnOp(opr, e1, t)) =
      let
        val c1 = gen_const' e1
        val t1 = get_type e1
      in
        case opr of
             Ast.NEG => ((Eq(t, Int, NEW))::(Eq t1, Int, NEW))@c1
           | Ast.NOT => ((Eq(t, Bool, NEW))::(Eq t1, Bool, NEW))@c1
           | Ast.HEAD => (Eq(t1, List t, NEW))::@c1
           | Ast.TAIL => (Eq(t, t1, NEW))::@c1
      end
    | gen_const' (BinOp(opr, e1, e2, t)) =
      let 
        val c1 = gen_const' e1
        val c2 = gen_const' e2
        val t1 = get_type e1
        val t2 = get_type e2
      in
        case opr of
             (Ast.PLUS | Ast.SUB | Ast.TIMES | Ast.DIV) =>
             ((Eq(t, Int, NEW))::(Eq(t1, Int, NEW))::(Eq(t2, Int, NEW)))
             @c1@c2
           | (Ast.LT | Ast.LE | Ast.GT | Ast.GE | Ast.EQ | Ast.NE) =>
             ((Eq(t, Bool, NEW))::(Eq(t1, Int, NEW))::(Eq(t2, Int, NEW)))
             @c1@c2
           | (Ast.AND | Ast.OR) =>
             ((Eq(t, Bool, NEW))::(Eq(t1, Bool, NEW))::(Eq(t2, Bool, NEW)))
             @c1@c2
           | Ast.CONS =>
             [Eq(t2, List t1, NEW)]@c1@c2
      end
    | gen_const' (Cond(e1, e2, e3, t)) =
      let
        val c1 = gen_const' e1
        val c2 = gen_const' e2
        val c3 = gen_const' e3
        val t1 = get_type e1
        val t2 = get_type e2
        val t3 = get_type e3
      in
        ((Eq(t1, Bool, NEW))::(Eq(t, t2, NEW))::(Eq(t2, t3, NEW)))
        @c1@c2@c3
      end
    | gen_const' (Abs(x, t, e, t')) =
      let
        val c1 = gen_const' e
        val t1 = get_type e
      in
        (Eq(t', Arrow(t, t1, NEW)))@c1
      end
    | gen_const' (App(e1, e2, t)) =
      let
        val c1 = gen_const' e1
        val c2 = gen_const' e2
        val t1 = get_type e1
        val t2 = get_type e2
      in
        (Eq(t1, Arrow(t2, t, NEW)))@c1@c2
      end

  (* occurs a T is true if var a occurs in t T, false o/w. *)
  fun occurs a (V(b)) = 
      if a = b then true else false
    | occurs a (Int | Bool) = false
    | occurs a (Arrow(t1, t2)) = occurs a t1 orelse occurs a t2
    | occurs a (List b) = occurs a b

  
  (* apply_sub sub (Eq(a, b, status)) is Eq(a', b', status) where
  * a' and b' are the result of applying sub to a and b.
  *)
  fun apply sub (Eq(a, b, status)) =
  let 
    (* apply2t sub tp is the t resulting from applying s sub to t tp. *)
    fun apply2t (Sub(x, y)) (V z) = if x = z then V y else V z
    | apply2t _ Int = Int
    | apply2t _ Bool = Bool
    | apply2t sub (Arrow(x, y)) =
      let
        val x' = apply2t sub x
        val y' = apply2t sub y
      in
        Arrow(x', y')
      end
    | apply2t sub (List x) =
      let 
        val x' = apply2t sub x
      in
        List x'
      end

    val a' = apply2t sub a
    val b' = apply2t sub b
  in
    Eq(a', b', status) 
  end

  (* apply_comp subs (Eq(a, b, NEW)) is (Eq(a', b', NEW), subs) 
  * where a' and b' are the results of applying each s in s list subs 
  * one at a time in reverse order to a and b, or,
  *
  * apply_comp subs (Eq(a, b, DONE)) is (Eq(a', b', DONE), subs) where a' and 
  * b' are the same as above, or
  *
  * apply_comp subs (Eq(a, b, ACTIVE)) is (Eq(a', b', DONE), subs') where
  * a' and b' are the result of applying each s in subs except the last
  * to a and b, and subs' is subs with the last element removed.
  *)
  fun apply_comp [] x = (x, [])
    | apply_comp (sub::[]) (Eq(a, b, ACTIVE)) = (Eq(a, b, DONE), [])
    | apply_comp (sub::subs) (Eq(a, b, status)) =
      let
        val eqn_subs = apply_comp subs (Eq(a, b, status))
        val eqn' = apply sub (#1 eqn_subs)
      in
        (eqn', sub::(#2 eqn_subs))
      end

  (* unify c is a solved form of t_eq list c if c has an mgu. If c has
  * no unifier, raises infer error.
  *)
  fun unify c =
  let
    fun unify' [] [] _ _ = []
      | unify' [] seen _ false = seen
      | unify' [] seen sub true = unify' (rev seen) [] sub false
      | unify' [c::cs] seen sub cont = 
        let
          val eq_sub = apply_comp sub c
          val c' = #1 eq_sub
          val sub' = #2 eq_sub
        in
          case c' of
               Eq(Arrow(a, b), Arrow(a', b'), _) =>
               unify' cs ((Eq(a, a', NEW))::(Eq(b, b', NEW))::seen) sub' true
             | (Eq(Arrow(_, _), List _, _) | Eq(List _, Arrow(_, _), _)) =>
                 raise infer_error "Expression cannot be typed."
             | Eq(List a, List b, _) =>
                 unify' cs ((Eq a, b, NEW)::seen) sub' true
             | Eq(List a, Var b, _) =>
                 unify' cs ((Eq(Var b, List a, NEW))::seen) sub' true
             | Eq(Arrow(a, b), Var c, _) =>
                 unify' cs ((Eq(Var c, Arrow(a, b), NEW))::seen) sub' true
             | Eq(Var a, Var b, NEW) =>
                 if a = b then unify' cs seen sub' cont
                 else unify' cs ((Eq(Var a, Var b, ACTIVE))::seen)
                      (sub'(a, Var b))::sub' true
             | Eq(Var a, b, NEW) =>
                 if occurs a b then raise 
                    infer_error "Expression cannot be typed."
                 else
                   unify' cs ((Eq(Var a, b, ACTIVE))::seen)
                   ((sub'(a, b))::sub') true
             | _ => unify' cs (c'::seen) sub' cont
        end
  in
    unify' c [] [] true
  end

  (* infer e => the most general type of e, inferred using Hindley-Milner.
  *  Raises infer_error if no type can be inferred for e.
  *)
  fun infer e =
  let
    val e' = label_ast e
    val t = get_type e'
    val c = gen_const e'
    val u = unify c
    
    (* get_type a u is a' where a' is the LHS of the equation in u that has
    * RHS a, if one exists, and a o/w.
    *)
    fun get_type a [] = a
      | get_type a ((Eq(b, c, _))::us) =
        if a = b then c else get_type a us
  in
    t
  end

  (* toString s => a fully-parenthesized string representation of the
  *  type s.
  *)
end
