structure Tests =
struct

  structure Ast = Ast
  structure Lexers = Lexers(L1Lex)

  structure L1Parse = L1Parse : PARSE
  open L1Parse

  structure L1Cbv = L1Cbv : EVAL
  open L1Cbv

  structure U = UnitTest


  val sl = fn s => Lexers.string_lexer s
  val fl = fn f => Lexers.file_lexer f

  fun do_test_ast(name, test, exp) = 
    U.do_test(name, fn () => parse_expression (sl test), exp, Ast.ast2str)

  fun do_test_eval(name, test, exp) =
    U.do_test(name, 
              fn () => value2ast (eval_expr (
                            parse_expression (sl test))), exp, Ast.ast2str)

    fun do_test_file_eval filename exp =
      U.do_test(filename, 
                fn () => value2ast (eval_pgm (
                            parse_program (fl ("test_files/" ^ filename)))),
                exp,
                Ast.ast2str)

  val test_ast = fn () => (

    (* Parsing tests. *)
    do_test_ast("Ident1", "x ;" , Ast.Ident("x")) ;

    do_test_ast("Ident2", "xyz ;", Ast.Ident("xyz")) ;

    do_test_ast("Num. const.", "5 ;", Ast.Number(5)) ;

    do_test_ast("Bool1", "x andalso y;",
      Ast.BinOp(Ast.AND, Ast.Ident "x", Ast.Ident "y")) ;
    do_test_ast("Bool4", "not x andalso y;",
      Ast.BinOp(Ast.AND, Ast.UnOp(Ast.NOT, Ast.Ident "x"), Ast.Ident "y")) ;
    do_test_ast("Bool5", "x < y orelse z < y;",
      Ast.BinOp(Ast.OR,
                Ast.BinOp(Ast.LT, Ast.Ident "x", Ast.Ident "y"),
                Ast.BinOp(Ast.LT, Ast.Ident "z", Ast.Ident "y"))) ;

    do_test_ast("List 1", "[];", Ast.NilList) ;
    do_test_ast("List 2", "2 :: 3 :: [];",
      Ast.BinOp(Ast.CONS, Ast.Number 2,
                   Ast.BinOp(Ast.CONS, Ast.Number 3, Ast.NilList))) ;
    do_test_ast("List 5", "5 + 3 :: [];", 
      Ast.BinOp(Ast.CONS,
                Ast.BinOp(Ast.PLUS, Ast.Number 5, Ast.Number 3),
                Ast.NilList)) ;
    do_test_ast("List 7", "((fn x => fn y => x + y)(2)) :: [];",
      Ast.BinOp(Ast.CONS,
                Ast.App(Ast.Abs("x",
                                Ast.Abs("y",
                                        Ast.BinOp(Ast.PLUS, 
                                                  Ast.Ident "x",
                                                  Ast.Ident "y"))),
                        Ast.Number 2),
                Ast.NilList)) ;

    do_test_ast("Arith .9", "3 + 5;", 
        Ast.BinOp(Ast.PLUS, Ast.Number(3), Ast.Number(5))) ;

    do_test_ast("Arith 1", "x * 3 + 4 / 5;",
      Ast.BinOp(Ast.PLUS, Ast.BinOp(Ast.TIMES, Ast.Ident("x"), Ast.Number(3)),
      Ast.BinOp(Ast.DIV, Ast.Number(4),
      Ast.Number(5)))) ;
    do_test_ast("Arith 3", "x * ((3+4)/5);",
      Ast.BinOp(Ast.TIMES,
                Ast.Ident("x"),
                Ast.BinOp(Ast.DIV,
                          Ast.BinOp(Ast.PLUS,
                                    Ast.Number 3, Ast.Number 4),
                          Ast.Number 5))) ;

    do_test_ast("NEG 1", "~3 ;", 
      Ast.UnOp(Ast.NEG, Ast.Number(3))) ;
    do_test_ast("NEG 2", "~(2+5) ;", 
      Ast.UnOp(Ast.NEG,
               Ast.BinOp(Ast.PLUS, Ast.Number(2), Ast.Number(5)))) ;

    do_test_ast("NumRel2", "x+y >= z-y;",
      Ast.BinOp(Ast.GE,
                Ast.BinOp(Ast.PLUS, Ast.Ident "x", Ast.Ident "y"),
                Ast.BinOp(Ast.SUB, Ast.Ident "z", Ast.Ident "y"))) ;


    do_test_ast("Cond2", "if 5 > 7 then 12 else zed fi;",
        Ast.Cond(Ast.BinOp(Ast.GT, Ast.Number(5), Ast.Number(7)), 
                 Ast.Number(12), 
                 Ast.Ident("zed"))) ;

    do_test_ast("Abs0", "fn x => x;", Ast.Abs("x", Ast.Ident("x"))) ;

    do_test_ast("Abs1", "fn x => x + 3;", Ast.Abs("x",
    Ast.BinOp(Ast.PLUS, Ast.Ident("x"),
    Ast.Number(3)))) ;

    do_test_ast("Abs2", "fn x => fn y => x + y;",
    Ast.Abs("x", Ast.Abs("y", Ast.BinOp(Ast.PLUS,
    Ast.Ident("x"), Ast.Ident("y"))))) ;

    do_test_ast("App 5", "(fn x => x) 3 + 4 ;",
      Ast.BinOp(Ast.PLUS,
                Ast.App(Ast.Abs("x", Ast.Ident "x"), Ast.Number 3), 
                Ast.Number 4)) ;

    true
  )

  val test_eval = fn () => (
    do_test_eval("Eval num 1", "5;", Ast.Number(5)) ;
    do_test_eval("Eval true", "true;", Ast.Boolean(true)) ;
    do_test_eval("Eval arith 2", "2 - 2;", Ast.Number(0)) ;
    do_test_eval("Eval cond. 2", "if false then 0 else 1 fi;", Ast.Number(1)) ;
    do_test_eval("Eval cond. 3", "if 3 <= 5 then 0 else 1 fi;", Ast.Number(0)) ;

    do_test_eval("Eval list 1", "[];", Ast.NilList) ;
    do_test_eval("Eval list 2", "1 :: [];", 
        Ast.BinOp(Ast.CONS, Ast.Number(1), Ast.NilList)) ;
    do_test_eval("Eval list 3", "1 :: 2 :: [];",
        Ast.BinOp(Ast.CONS, 
                  Ast.Number(1), 
                  Ast.BinOp(Ast.CONS, Ast.Number(2), Ast.NilList))) ;
    do_test_eval("Eval list 5", "((fn x => fn y => x + y)(2)) :: [];",
        Ast.BinOp(Ast.CONS, Ast.Abs("y", 
                           Ast.BinOp(Ast.PLUS, Ast.Number(2), Ast.Ident("y"))),
                           Ast.NilList)) ;
                    
    do_test_eval("Eval hd/tl 3", "hd tl (1 :: 2 :: []);", Ast.Number(2)) ;

    do_test_eval("Eval abs 1", "fn x => x;", 
        Ast.Abs("x", Ast.Ident("x"))) ;
    do_test_eval("Eval abs 3", "(fn x => fn y => x + y)(2);",
        Ast.Abs("y", Ast.BinOp(Ast.PLUS, Ast.Number(2), Ast.Ident("y")))) ;

    do_test_eval("Eval app 3", "(fn x => x)(fn y => y + y);",
        Ast.Abs("y", Ast.BinOp(Ast.PLUS, Ast.Ident("y"),
        Ast.Ident("y")))) ;

    true
  )

  fun test_eval_file() = 
  let
    val files_results = [
        ("t3.l1", Ast.Number 8)
    ]
    fun test_files [] = true
      | test_files ((test, res) :: frs) = 
            (do_test_file_eval test res ; test_files frs)
  in
    test_files files_results
  end


  fun run_tests(arg0 : string, args : string list) = 
    BackTrace.monitor(fn () =>
      (U.run_tests(fn () => (test_ast() ; test_eval() ; test_eval_file() )) ; 0)
    )

end
