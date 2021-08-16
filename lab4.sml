(***********************************************************)
(*       LISP interpreter                                  *)
(*                                                         *)
(*       Carter King                                       *)
(*       8 April 2021                                      *)
(*       Lab 4 Reference Skeleton, COMP 360                *)
(*                                                         *)
(***********************************************************)

exception EvalError of string;
exception LexerError;
exception ParseOK;
exception ParseError of string;
exception UnboundVar;
exception ParameterMismatch;

(***********************************************************)
(* type declarations                                       *)
(***********************************************************)

datatype sign =
   Plus
 | Minus;

datatype atom =
   T
 | NIL
 | Int of int
 | Ident of string;

datatype token =
   Lparen
 | Rparen
 | Dot
 | Sign of sign
 | Atom of atom;

datatype sexp =
   AtomExp of atom
 | Sexp of sexp * sexp;

let
    (***********************************************************)
    (* globals                                                 *)
    (***********************************************************)
    val lineno = ref 1;
    val dlist = ref (AtomExp(NIL));

    (***********************************************************)
    (* printing functions                                      *)
    (***********************************************************)

    (* function: print_tokens - prints out a token stream  *)
    fun print_tokens [] = print("\n")
      | print_tokens (Lparen :: t) = (print("Lparen "); print_tokens(t))
      | print_tokens (Rparen :: t) = (print("Rparen "); print_tokens(t))
      | print_tokens (Dot :: t) = (print("Dot "); print_tokens(t))
      | print_tokens (Sign(Plus) :: t) = (print("Plus "); print_tokens(t))
      | print_tokens (Sign(Minus) :: t) = (print("Minus "); print_tokens(t))
      | print_tokens (Atom(a) :: t) =
      (case a of
             T => (print("Atom(T) "); print_tokens(t))
           | NIL => (print("Atom(NIL) "); print_tokens(t))
           | Int i => (print("Atom(Int(" ^ Int.toString(i) ^ ")) "); print_tokens(t))
           | Ident s => (print("Atom(Ident(" ^ s ^ ")) "); print_tokens(t)));

    (* function: string_of_op -  converts an operator token to a string *)
    fun string_of_op Plus = "+"
     |  string_of_op Minus = "-";


    (* function: is_list - predicate function returning true if s-expression is a list *)
    fun is_list (Sexp(h, AtomExp(NIL))) = true
     |  is_list (Sexp(h, t)) = is_list t
     |  is_list _ = false;


    (* function: string_of_atom - converts a primitive atom to a string *)
    fun string_of_atom (T) = "t"
     |  string_of_atom (NIL) = "nil"
     |  string_of_atom (Int(i)) = Int.toString i
     |  string_of_atom (Ident(i)) = i;

    (* function: string_of_token - converts a lexer token to a string *)
    fun string_of_token (Lparen) = "("
     |  string_of_token (Rparen) = ")"
     |  string_of_token (Dot) = "."
     |  string_of_token (Sign(s)) = string_of_op s
     |  string_of_token (Atom(a)) = string_of_atom a;

    (* function: print_list - prints an s-expression in list format *)
    fun print_list (AtomExp(NIL)) = ()
     |  print_list (AtomExp(a)) = print(string_of_atom a)
     |  print_list (Sexp(h,AtomExp(NIL))) = print_sexp h
     |  print_list (Sexp(h,t)) =
           (print_sexp h;
            print " ";
            print_list t)

    (* function: print_sexp - prints an s-expression in either dotted or list format *)
    and print_sexp s =
      if (is_list s) then
         (print "(";
         print_list s;
         print ")")
      else
        (case s of
              AtomExp(a) => print (string_of_atom a)
            | Sexp(h,t) =>
                (print "(";
                print_sexp h;
                print " . ";
                print_sexp t;
                print ")"));


    (***********************************************************)
    (* lexer implementation                                    *)
    (***********************************************************)

    (* function: spaces - eats whitespace between tokens *)
    fun spaces (#" " :: t)  = spaces t
      | spaces (#"\t" :: t) = spaces t
      | spaces (#"\n" :: t) = (lineno := !lineno + 1; spaces t)
      | spaces l = l;

    (* function: char_to_int - converts character to integer with error checking *)
    fun char_to_int(c) =
      let
        val copt = Int.fromString(Char.toString(c))
      in
        (case copt of
              SOME(vv) => vv
            | NONE => raise LexerError)
      end;


    (* function: lexid - assembles characters into an Ident token *)
    fun lexid (s, []) = (s, [])
      | lexid (s, h::t) =
      if Char.isAlphaNum(h) then
        lexid(s ^ Char.toString(h), t)
      else
        (s, h::t);

    (* function: lexint - assembles digits into an Int token *)
    fun lexint (v, []) = (v, [])
      | lexint (v, h::t) =
      if Char.isDigit(h) then
        lexint((10*v)+char_to_int(h), t)
      else
        (v, h::t);

    (* function: lexer - main tokenizer driver; maps character stream to token stream *)
    fun  lexer( #"(" :: t) =   Lparen :: lexer(t)
      |  lexer( #")" :: t) =  Rparen :: lexer(t)
      |  lexer( #"." :: t) =  Dot :: lexer(t)
      |  lexer( #"-" :: t) =  Sign(Minus) :: lexer(t)
      |  lexer( #"+" :: t) =  Sign(Plus) :: lexer(t)
      |  lexer( h::t ) =
             if Char.isAlpha(h) then
               let
                 val (idstr,tt) = lexid(Char.toString(h), t)
               in
                 (case (String.map Char.toLower idstr) of
                       "nil" => Atom(NIL) :: lexer(tt)
                     | "t"   => Atom(T) :: lexer(tt)
                     | _     => Atom(Ident(idstr)) :: lexer(tt))
               end
             else if Char.isDigit(h) then
               let
                 val (intval, tt) = lexint(char_to_int(h), t)
               in
                 Atom(Int(intval)) :: lexer(tt)
               end
             else if (h = #"\n") then
               (lineno := !lineno + 1; lexer(spaces(t)))
                  else if Char.isSpace(h) then
                    lexer(spaces(t))
                  else
                    (print ("ERROR: Illegal character on line " ^ Int.toString(!lineno) ^ ": " ^ Char.toString(h));
                              raise LexerError)
      |   lexer [] = [];


    (***********************************************************)
    (* parser implementation                                   *)
    (***********************************************************)

    (* function: check_sign - both validates and combines sign and integer token pairs *)
    fun check_sign (Sign(Minus)::(Atom(Int(i)))::rest) = (AtomExp(Int(~i)),rest)
     |  check_sign (Sign(Plus)::(Atom(Int(i)))::rest) = (AtomExp(Int(i)),rest)
     |  check_sign _ = raise ParseError "+/- sign may only be used with integer literals";


    (* function: parse_sexp - top-level parser: takes stream of tokens, returns sexp-tree *)
    (* S ::= E *)
    fun parse_sexp [] = raise ParseOK
     |  parse_sexp exp = parse_exp exp

    (* E ::= atom | '(' X          *)
    and parse_exp (Lparen::rest) = parse_x rest
     |  parse_exp (Sign(s)::rest) = check_sign (Sign(s)::rest)
     |  parse_exp (Atom(a)::rest) = (AtomExp(a), rest)
     |  parse_exp _ = raise ParseError "parse ended expecting '(' or an atom expression"

    (* X ::= E Y | ')'   *)
    and parse_x (Rparen::rest) = (AtomExp(NIL),rest)
     |  parse_x sexp =
        let
          val (e,rest1) = parse_exp sexp
          val (y,rest2) = parse_y   rest1
        in
          (Sexp(e,y), rest2)
         end

    (* Y ::= '.' E ')' | R ')'    *)
    and parse_y (Dot::rest) =
        let
          val (e, rest1) = parse_exp rest
          val rest2 = parse_rparen rest1
        in
          (e,rest2)
        end
      |  parse_y sexp =
         let
           val (r, rest1) = parse_r sexp
           val rest2 = parse_rparen rest1
        in
          (r,rest2)
        end

    (* R ::= E R | empty  *)
    and parse_r (Lparen::rest) =
        let
          val (e,rest1) = parse_exp (Lparen::rest)
          val (r,rest2) = parse_r   rest1
         in
           (Sexp(e,r), rest2)
         end
      |  parse_r (Sign(s)::rest) =
         let
           val (e,rest1) = parse_exp (Sign(s)::rest)
           val (r,rest2) = parse_r   rest1
         in
           (Sexp(e,r), rest2)
         end
     | parse_r (Atom(a)::rest) =
       let
         val (e,rest1) = parse_exp (Atom(a)::rest)
         val (r,rest2) = parse_r   rest1
       in
         (Sexp(e,r), rest2)
       end
     | parse_r rest = (AtomExp(NIL),rest)

    (* convenience production for right parens *)
    and parse_rparen (Rparen::rest) = rest
     |  parse_rparen rest = raise ParseError "parser ended expecting ')'";



    (*****************************************)
    (* interpretation functions              *)
    (*****************************************)

    (* function: bound - checks that referenced variables are bound in a-list or d-list,  *)
    fun bound name (AtomExp(NIL)) = false
      | bound name (Sexp(Sexp(AtomExp(Ident(formal)), value), rest)) = if name = formal then true else bound name rest
      | bound name _ = raise EvalError "improper a-list/d-list format checked by bound"
    ;
    (* function: getval - returns the value of a variable from the a-list or d-list*)
    fun getval name (AtomExp(NIL)) = raise UnboundVar
      | getval name (Sexp(Sexp(AtomExp(Ident(formal)), value), rest)) = if name = formal then value else getval name rest
      | getval name _ = raise EvalError "improper a-list/d-list format received by getval"
    ;

    (* function: check_formal - checks function parameters from matching T or NIL or not having uniquye identifiers *)
    fun check_formal (AtomExp(NIL))                   = true
      | check_formal (Sexp(AtomExp(Ident("t")), t))   = raise EvalError "can't use t as variable name"
      | check_formal (Sexp(AtomExp(Ident("nil")), t)) = raise EvalError "can't use nil as variable name"
      | check_formal (Sexp(formal, rest)) = 
        let 
          fun repeat_param name (AtomExp(NIL))          = true
            | repeat_param name (Sexp(next_name, rest)) = if name = next_name then raise EvalError "can't repeat parameter names"
                                                          else repeat_param name rest
            | repeat_param name _ = raise EvalError "can't check formal for repeat identifier"
        in 
          (repeat_param formal rest;
          check_formal rest)
        end
      | check_formal _ = raise EvalError "improper parameter list sent to check_formal"
    ;

    (* function: eval_defun - checks defun usage and adds function def to the global d-list *)
    fun eval_defun (Sexp(AtomExp(Ident("defun")), t))  a d = raise EvalError "can't redefine defun"
      | eval_defun (Sexp(AtomExp(Ident("cond")), t))   a d = raise EvalError "can't redefine cond"
      | eval_defun (Sexp(AtomExp(Ident("quote")), t))  a d = raise EvalError "can't redefine quote"
      | eval_defun (Sexp(name, Sexp(formals, body)))   a d =  
          if check_formal formals then (d := (Sexp((Sexp(name, Sexp(formals, body))), (!d))); name)
          else raise EvalError "Incorrect function definition"
      | eval_defun _ a d = raise EvalError "improper defining of function"
    
    ;



    (* function: addpairs - checks function parameters and binds formals to actuals *)
    fun addpairs (Sexp(h, t)) (AtomExp(NIL)) z       = raise ParameterMismatch
      | addpairs (AtomExp(NIL)) (Sexp(h, t)) z       = raise ParameterMismatch
      | addpairs (Sexp(x, rest1)) (Sexp(y, rest2)) z = Sexp(Sexp(x, y), addpairs rest1 rest2 z)
      | addpairs (AtomExp(NIL)) (AtomExp(NIL)) z     = AtomExp(NIL)
      | addpairs _ _ z = raise EvalError "Cannot bind formals to actuals"
    
    ;

    (* function: eval - top-level s-expression evaluation loop *)
    fun eval (AtomExp(s)) a d = (case s of
             T        => (AtomExp(T))
           | NIL      => (AtomExp(NIL))
           | Int(x)   => (AtomExp(Int(x)))
           | Ident(x) => if bound x a then getval x a else raise UnboundVar)
      | eval (Sexp(AtomExp(Ident("quote")), Sexp(h, t))) a d = h
      | eval (Sexp(AtomExp(Ident("defun")), t)) a d = eval_defun t a d
      | eval (Sexp(AtomExp(Ident("cond")), t))  a d = evcon t a d
      | eval (Sexp(AtomExp(x), AtomExp(NIL))) a d = eval (AtomExp(x)) a d
      | eval (Sexp(name, args)) a d = apply name (evlist args a d) a d
      (*| eval (Sexp(name, Sexp(args, t)))  a d = apply name (evlist args a d) a d*)
      (*| eval (Sexp(Sexp(name, args), t)) a d = apply name (evlist args a d) a d*)
      (*| eval _ a d = raise EvalError "couldn't evaluate arguments"*)
              

    (* function: evcon - evaluates a COND statement *)
    and evcon (AtomExp(NIL)) a d = raise EvalError "conditional has no true statement"
      | evcon (Sexp(Sexp(expression, statement), rest)) a d = if eval (expression) a d = AtomExp(T) then eval (statement) a d                                                               else evcon (rest) a d
      | evcon _ a d = raise EvalError "incorrect cond formatting"

    (* function: evlist - evaluates a list of expressions and returns a list of results *)
    and evlist (AtomExp(NIL)) a d     = AtomExp(NIL)
      | evlist (Sexp(head, tail)) a d = Sexp(eval (head) a d, evlist (tail) a d)
      | evlist _ a d = raise EvalError "improper list evaluation"

    (* function: apply - performs function application, handles built-ins *)
    and apply (AtomExp(Ident("car"))) (Sexp(Sexp(x, y), t)) a d = x
      | apply (AtomExp(Ident("cdr"))) (Sexp(Sexp(x, y), t))  a d      = y
      | apply (AtomExp(Ident("cons"))) (Sexp(x, Sexp(y, z))) a d = (Sexp(x, y))
      | apply (AtomExp(Ident("atom"))) (Sexp(AtomExp(x), AtomExp(NIL))) a d                       = (AtomExp(T))
      | apply (AtomExp(Ident("atom"))) _ a d                = (AtomExp(NIL))
      | apply (AtomExp(Ident("null"))) (AtomExp(NIL)) a d   = (AtomExp(T))
      | apply (AtomExp(Ident("null"))) _ a d                = (AtomExp(NIL))
      | apply (AtomExp(Ident("int"))) (Sexp(AtomExp(Int(x)), AtomExp(NIL))) a d = (AtomExp(T))
      | apply (AtomExp(Ident("int"))) _ a d                 = (AtomExp(NIL))
      | apply (AtomExp(Ident("plus"))) (Sexp(AtomExp(Int(x)), Sexp(AtomExp(Int(y)), t))) a d      = (AtomExp(Int(x + y)))
      | apply (AtomExp(Ident("plus"))) _ a d                = raise ParameterMismatch
      | apply (AtomExp(Ident("minus"))) (Sexp(AtomExp(Int(x)), Sexp(AtomExp(Int(y)),t))) a d      = (AtomExp(Int(x - y)))
      | apply (AtomExp(Ident("minus"))) _ a d               = raise ParameterMismatch
      | apply (AtomExp(Ident("times"))) (Sexp(AtomExp(Int(x)), Sexp(AtomExp(Int(y)), t))) a d     = (AtomExp(Int(x * y)))
      | apply (AtomExp(Ident("times"))) _ a d               = raise ParameterMismatch
      | apply (AtomExp(Ident("quotient"))) (Sexp(AtomExp(Int(x)), Sexp(AtomExp(Int(y)), t))) a d  = (AtomExp(Int(x div y)))
      | apply (AtomExp(Ident("quotient"))) _ a d            = raise ParameterMismatch
      | apply (AtomExp(Ident("remainder"))) (Sexp(AtomExp(Int(x)), Sexp(AtomExp(Int(y)), t))) a d = (AtomExp(Int(x mod y)))
      | apply (AtomExp(Ident("remainder"))) _ a d           = raise ParameterMismatch
      | apply (AtomExp(Ident("less"))) (Sexp(AtomExp(Int(x)), Sexp(AtomExp(Int(y)), t))) a d     
                                                            =  if x < y then (AtomExp(T)) else (AtomExp(NIL))
      | apply (AtomExp(Ident("less"))) _ a d                = raise ParameterMismatch
      | apply (AtomExp(Ident("greater"))) (Sexp(AtomExp(Int(x)), Sexp(AtomExp(Int(y)), t))) a d  
                                                            = if x > y then (AtomExp(T)) else (AtomExp(NIL))
      | apply (AtomExp(Ident("eq"))) (Sexp(AtomExp(x), Sexp(AtomExp(y), t))) a d        
                                                            = if x = y then (AtomExp(T)) else (AtomExp(NIL))
      | apply (AtomExp(Ident("eq"))) _ a d                  = raise ParameterMismatch
      | apply (AtomExp(Ident(exp))) x a d = 
            let 
              val formalsAndBody = getval exp (!d)
            in
              (case formalsAndBody of 
                  Sexp(formals, Sexp(body, ta)) => eval body (addpairs formals x a) d
                | _ => raise EvalError "Malformed D-List entry")
            end
      | apply _ _ a d = raise EvalError "Cannot compute call to apply"
    ;


    (*****************************************)
    (* helper routines                       *)
    (*****************************************)

    fun get_sexp [] = (AtomExp(NIL),[])
     |  get_sexp s = parse_sexp s;

    fun next_sexp [] = OS.Process.exit(OS.Process.success)
      | next_sexp s =
        let
          val (e,rest) = get_sexp s
          val e' = eval e (AtomExp(NIL)) dlist
        in
          (print_sexp e';
          print "\n";
          next_sexp rest
          handle ParseError msg => print ("Parse Error: " ^ msg ^ "\n")
               | EvalError msg =>  print ("Evaluation Error: " ^ msg ^ "\n")
               | ParseOK => OS.Process.exit(OS.Process.success))
     end

    fun reader(copt: char option, is, l) =
      case copt of
           NONE    => (TextIO.closeIn is; l)
         | SOME(c) => reader (TextIO.input1 is, is, (l@[c]));


    (*****************************************)
    val args = CommandLine.arguments()
    val ins = TextIO.openIn(hd(args))
    val (sexp,ts) = get_sexp(lexer(reader(TextIO.input1 ins, ins, [])))
    val se' = (eval sexp (AtomExp(NIL)) dlist)


in
    (*****************************************)
    (* main                                  *)
    (*****************************************)

    print_sexp(se');
    print "\n";
    next_sexp ts
end
handle ParseError msg =>  print ("Parse Error: " ^ msg ^ "\n")
     | EvalError msg =>  print ("Evaluation Error: " ^ msg ^ "\n")
     | ParseOk =>  OS.Process.exit(OS.Process.success);
