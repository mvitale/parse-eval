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


  (* The type of labeled ast nodes. *)
  datatype l_expr = Ident of ident*t | Number of int*t | Boolean of bool*t |
                    UnOp of Ast.unop*l_expr*t | 
                    BinOp of Ast.binop*l_expr*l_expr*t | NilList of t |
                    Cond of l_expr*l_expr*l_expr*t | 
                    Abs of ident*t*l_expr*t |
                    App of l_expr*l_expr*t

  (* The type of our representation of a formal type equation. *)
  datatype t_eq = Eq of t*t

  (* An environment maps an equality type to a type. *)
  type (''a,'b) env = ''a -> 'b

  (* The empty environment. *)
  val env_empty = (fn v => raise env_error) : (''a,'b) env

  (* env_update (env, id, v) = env', where env' = [v/id]env. *)
  fun env_update(e, id, v) = fn x => if x = id then v else e(x)

  (* env_get (env, id) = env(id) (i.e., the value id is mapped to by env. *)
  fun env_get(e, id) = e(id)

  (* get_type e is the type with which l_expr e is labeled. *)
  fun get_type (Ident(_, t)) = t
    | get_type (Number(_, t)) = t
    | get_type (Boolean(_, t)) = t
    | get_type (UnOp(_, _, t)) = t
    | get_type (BinOp(_, _, _, t)) = t
    | get_type (NilList(t)) = t
    | get_type (Cond(_, _, _, t)) = t
    | get_type (Abs(_, _, _, t)) = t
    | get_type (App(_, _, t)) = t

  (* label_ast e is the l_expr corresponding to Ast.expr e with each node 
  * labeled with generic types. If a node must have a list type, it is given
  * a generic list type.
  *)
  fun label_ast e =
  let
    fun label_ast' (Ast.Ident(x)) env fresh abs =
        let
          val tx = env_get(env, x) handle env_error =>
          if abs then raise infer_error "Unbound identifier." else fresh
        in
          (Ident(x, V tx), env_update(env, x, tx), 
           if tx = fresh then fresh+1 else fresh)
        end
      | label_ast' (Ast.Number(n)) env fresh abs =
        (Number(n, V fresh), env, fresh+1)
      | label_ast' (Ast.Boolean(b)) env fresh abs =
        (Boolean(b, V fresh), env, fresh+1)
      | label_ast' (Ast.UnOp(opr, e)) env fresh abs =
        let
          val (e', env', fresh') = label_ast' e env (fresh+1) abs
        in
          case opr of
               Ast.TAIL => (UnOp(opr, e', List(V fresh)), env', fresh')
             | _ => (UnOp(opr, e', V fresh), env', fresh')
        end
      | label_ast' (Ast.BinOp(opr, e1, e2)) env fresh abs =
        let
          val (e1', env', fresh') = label_ast' e1 env (fresh+1) abs
          val (e2', env'', fresh'') = label_ast' e2 env' fresh' abs
        in
          case opr of
               Ast.CONS =>
               (BinOp(opr, e1', e2', List(V fresh)), env'', fresh'')
             | _ =>
               (BinOp(opr, e1', e2', V fresh), env'', fresh'')
        end
      | label_ast' Ast.NilList env fresh abs =
        (NilList(List(V fresh)), env, fresh+1)
      | label_ast' (Ast.Cond(e1, e2, e3)) env fresh abs =
        let
          val (e1', env', fresh') = label_ast' e1 env (fresh+1) abs
          val (e2', env'', fresh'') = label_ast' e2 env' fresh' abs
          val (e3', env''', fresh''') = label_ast' e3 env'' fresh'' abs
        in
          (Cond(e1', e2', e3', V fresh), env''', fresh''')
        end
      | label_ast' (Ast.Abs(x, e)) env fresh abs =
        let
          val env' = env_update(env, x, fresh+1)
          val (e', env'', fresh') = label_ast' e env' (fresh+2) true
        in
          (Abs(x, V(fresh+1), e', V fresh), env, fresh')
        end
      | label_ast' (Ast.App(e1, e2)) env fresh abs =
        let
          val (e1', env', fresh') = label_ast' e1 env (fresh+1) abs
          val (e2', env'', fresh'') = label_ast' e2 env' fresh' abs
        in
          (App(e1', e2', V fresh), env'', fresh'')
        end

    val (e', env, fresh) = label_ast' e env_empty 0 false
  in
    e'
  end

  (* gen_const e is a list of t_eq representing constraints generated from
  * l_expr e.
  *)
  fun gen_const e =
  let
    (* gen_const' e accum is a list of t_eq representing constraints
    * generated from e along with the equations in accum.
    *)
    fun gen_const' (Ident(_, _) | NilList(_)) accum = accum
      | gen_const' (Number(_, a)) accum = (Eq(a, Int))::accum
      | gen_const' (Boolean(_, a)) accum = (Eq(a, Bool))::accum
      | gen_const' (UnOp(opr, e, a)) accum =
        let
          val b = get_type e
          val accum' = 
            case opr of
                 Ast.NEG => (Eq(a, Int))::(Eq(b, Int))::accum
               | Ast.NOT => (Eq(a, Bool))::(Eq(b, Bool))::accum
               | Ast.HEAD => (Eq(b, List a))::accum
               | Ast.TAIL => (Eq(b, a))::accum (* a is already a list type *)
        in
          gen_const' e accum'
        end
      | gen_const' (BinOp(opr, e1, e2, a)) accum =
        let
          val b = get_type e1
          val c = get_type e2
          val accum' =
            case opr of
                 (Ast.PLUS | Ast.SUB | Ast.TIMES | Ast.DIV) =>
                 (Eq(a, Int))::(Eq(b, Int))::(Eq(c, Int))::accum
               | (Ast.LT | Ast.LE | Ast.GT | Ast.GE | Ast.EQ | Ast.NE) =>
                 (Eq(a, Bool))::(Eq(b, Int))::(Eq(c, Int))::accum
               | (Ast.AND | Ast.OR) =>
                 (Eq(a, Bool))::(Eq(b, Bool))::(Eq(c, Bool))::accum
               | Ast.CONS =>
                 (Eq(a, c))::(Eq(a, List b))::accum (* a is already a list type *)
          val accum'' = gen_const' e1 accum'
        in
          gen_const' e2 accum''
        end
      | gen_const' (Cond(e1, e2, e3, a)) accum =
        let
          val b = get_type e1
          val c = get_type e2
          val d = get_type e3
          val accum' = (Eq(b, Bool))::(Eq(c, d))::(Eq(a, c))::accum
          val accum'' = gen_const' e1 accum'
          val accum''' = gen_const' e2 accum''
        in
          gen_const' e3 accum'''
        end
      | gen_const' (Abs(x, a, e, b)) accum =
        let
          val c = get_type e
          val accum' = (Eq(b, Arrow(a, c)))::accum
        in
          gen_const' e accum'
        end
      | gen_const' (App(e1, e2, a)) accum =
        let
          val b = get_type e1
          val c = get_type e2
          val accum' = (Eq(b, Arrow(c, a)))::accum
          val accum'' = gen_const' e1 accum'
        in
          gen_const' e2 accum''
        end
  in
    gen_const' e []
  end

  (* occurs a b is true if var a occurs in t b, false o/w. *)
  fun occurs a (Int | Bool) = false
    | occurs a (V b) =
      if a = b then true else false
    | occurs a (Arrow(t1, t2)) = occurs a t1 orelse occurs a t2
    | occurs a (List b) = occurs a b

  fun occurs_eq a (Eq(t1, t2)) =
      occurs a t1 orelse occurs a t2

  (* occurs_any a bs is true if var a occurs in any b in bs, false o/w. *)
  fun occurs_any a [] = false
    | occurs_any a (b::bs) =
      occurs_eq a b orelse occurs_any a bs

  (* sub a b t is t' where t' is t with all occurrences of (V a) changed to
  * b.
  *)
  fun sub a b Int = Int
    | sub a b Bool = Bool
    | sub a b (V c) = if a = c then b else (V c)
    | sub a b (List c) = List(sub a b c)
    | sub a b (Arrow(t1, t2)) = Arrow(sub a b t1, sub a b t2)

  (* sub_eq a b (Eq(t1, t2)) is (Eq(t1', t2') where t1' and t2' are sub a b t1 and
  * sub a b t2.
  *)
  fun sub_eq a b (Eq(t1, t2)) =
  let
    val t1' = sub a b t1
    val t2' = sub a b t2
  in
    Eq(t1', t2')
  end

  (* sub_eqns a b eqns is eqns' resulting from applying sub_eq a b to each
  * element of eqns
  *)
  fun sub_eqns a b [] = []
    | sub_eqns a b (eq::eqns) =
      let
        val eq' = sub_eq a b eq
      in
        eq'::(sub_eqns a b eqns)
      end

  (* unify a eqns is the value of a under an mgu of eqns. If eqns cannot be
  * unified, raises infer_error.
  *)
  fun unify a eqns =
  let 
    fun get_type a [] = V a
      | get_type a ((Eq(V t1, t2))::eqs) =
        if a = t1 then t2
        else if (V a) = t2 then V t1
        else
          let
            val so_far = get_type a eqs
          in
            sub t1 t2 so_far
          end

    fun unify' [] accum =  accum
      | unify' ((Eq(Int, Int))::eqs) accum = unify' eqs accum
      | unify' ((Eq(Bool, Bool))::eqs) accum = unify' eqs accum
      | unify' ((Eq(Arrow(a, b), Arrow(a', b')))::eqs) accum =
        unify' ((Eq(a, a'))::(Eq(b, b'))::eqs) accum
      | unify' ((Eq(List a, List b))::eqs) accum =
        unify' ((Eq(a, b))::eqs) accum
      | unify' ((Eq(V a, b))::eqs) accum =
        if V a = b then unify' eqs accum
        else if occurs a b then raise infer_error "Equations cannot be unified."
        else if occurs_any a eqs then unify' (sub_eqns a b eqs) 
                ((Eq(V a, b))::accum)
        else unify' eqs ((Eq(V a, b))::accum)

      | unify' ((Eq(a, V b))::eqs) accum =
        unify' ((Eq(V b, a))::eqs) accum
      | unify' _ _ = raise infer_error "Equations cannot be unified."

    val result = unify' eqns []
  in
    get_type a result
  end  


  (* infer e => the most general type of e, inferred using Hindley-Milner.
  *  Raises infer_error if no type can be inferred for e.
  *)
  fun infer e =
  let
    val e' = label_ast e
    val t = get_type e'
    val c = gen_const e'
  in
    case t of 
         List(V a) => List(unify a c)
       | V a => unify a c
  end    
  
  (* toString s => a fully-parenthesized string representation of the
    *  type s.
    *)
  fun toString Int = "int"
    | toString Bool = "bool"
    | toString (V v) = "V"^(Int.toString v)
    | toString (Arrow(a, b)) =
      let
        val a' = toString a
        val b' = toString b
      in
        "("^a'^" -> "^b'^")"
      end
    | toString (List a) =
      let
        val a' = toString a
      in
        "["^a'^"]"
      end
      
end
