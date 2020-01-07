#use "reader.ml";;

type constant =
  | Sexpr of sexpr
  | Void

type expr =
  | Const of constant
  | Var of string
  | If of expr * expr * expr
  | Seq of expr list
  | Set of expr * expr
  | Def of expr * expr
  | Or of expr list
  | LambdaSimple of string list * expr
  | LambdaOpt of string list * string * expr
  | Applic of expr * (expr list);;

let rec expr_eq e1 e2 =
  match e1, e2 with
  | Const Void, Const Void -> true
  | Const(Sexpr s1), Const(Sexpr s2) -> sexpr_eq s1 s2
  | Var(v1), Var(v2) -> String.equal v1 v2
  | If(t1, th1, el1), If(t2, th2, el2) -> (expr_eq t1 t2) &&
                                            (expr_eq th1 th2) &&
                                              (expr_eq el1 el2)
  | (Seq(l1), Seq(l2)
    | Or(l1), Or(l2)) -> List.for_all2 expr_eq l1 l2
  | (Set(var1, val1), Set(var2, val2)
    | Def(var1, val1), Def(var2, val2)) -> (expr_eq var1 var2) &&
                                             (expr_eq val1 val2)
  | LambdaSimple(vars1, body1), LambdaSimple(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr_eq body1 body2)
  | LambdaOpt(vars1, var1, body1), LambdaOpt(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr_eq body1 body2)
  | Applic(e1, args1), Applic(e2, args2) ->
     (expr_eq e1 e2) &&
       (List.for_all2 expr_eq args1 args2)
  | _ -> false;;
	
                       
exception X_syntax_error;;

module type TAG_PARSER = sig
  val tag_parse_expression : sexpr -> expr
  val tag_parse_expressions : sexpr list -> expr list
end;; (* signature TAG_PARSER *)

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;  

(* work on the tag parser starts here *)

let not_reserved_word = fun sym -> not (List.mem sym reserved_word_list);;

let rec tag_proper_arguments = fun pairs ->
  match pairs with
  | Pair(Symbol(x), Nil) -> x :: []
  | Pair(Symbol(x), y) -> x :: (tag_proper_arguments y)
  | _ -> raise X_syntax_error;;

let rec tag_improper_mandatory_arguments = fun pairs ->
  match pairs with
  | Pair(Symbol(x), Pair(y, z)) -> x :: (tag_improper_mandatory_arguments (Pair(y, z)))
  | Pair(Symbol(x), Symbol(y)) -> x :: []
  | _ -> raise X_syntax_error

let rec proper_list list =
  match list with
  | Nil -> true
  | Pair(car, cdr) -> (proper_list(cdr))
  | _ -> false;;

let rec get_optional_arg args =
  match args with
  | Pair(Symbol(x), Pair(y, z)) -> (get_optional_arg (Pair(y, z)))
  | Pair(Symbol(x), Symbol(y)) -> y
  | _ -> raise X_syntax_error

let cdr = fun pair ->
  match pair with
  | Pair(x, y) -> y
  | _ -> raise X_syntax_error

(*const*)
let rec tag_parser = function
  | (*const*) Number(x) -> Const(Sexpr(Number(x)))
  | (*const*) Bool(x) -> Const(Sexpr(Bool(x)))
  | (*const*) Char(x) -> Const(Sexpr(Char(x)))
  | (*const*) String(x) -> Const(Sexpr(String(x)))
  | (*const*) TaggedSexpr(tag, Pair(Symbol("quote"), Pair(Nil, Nil))) -> Const(Sexpr(TaggedSexpr(tag, Nil)))
  | (*const*) TaggedSexpr(tag, sexp) -> (match sexp with
      | Pair(Symbol("quote"), Pair(exp, Nil)) -> Const(Sexpr(TaggedSexpr(tag, exp)))
      | Pair(Symbol("quote"), exp) -> Const(Sexpr(TaggedSexpr(tag, exp)))
      | _ -> Const(Sexpr(TaggedSexpr(tag, sexp))))
  | (*const*) Pair(Symbol("quote"), Pair(sexp, Nil)) ->
    (match sexp with
     | TaggedSexpr(tag, exp) -> Const(Sexpr(TaggedSexpr(tag, exp)))
     | _ -> Const(Sexpr(sexp)))
  | (*tag reg*) TagRef (tag) -> (Const(Sexpr (TagRef (tag))))
  | (*var*) Symbol(x) when (not_reserved_word x) -> Var(x)
  | (*if no else*) Pair (Symbol("if"), Pair(test, Pair(dit, Nil))) -> If(tag_parser test, tag_parser dit, Const(Void))
  | (*if else*) Pair(Symbol("if"), Pair(test, Pair(dit, Pair(dif, Nil)))) -> If(tag_parser test, tag_parser dit, tag_parser dif)
  | (*seq*) Pair(Symbol ("begin"), expr) -> (sequence expr)
  | (*set*) Pair(Symbol "set!", Pair(setVar, Pair(setValue, Nil))) -> Set(tag_parser setVar, tag_parser setValue)
  | (*define*) Pair(Symbol ("define"), restOfDefineExpr) -> define_tag_parser restOfDefineExpr
  | (*empty or*) Pair (Symbol "or", Nil) -> Const (Sexpr (Bool false))
  | (* 1 arg or*) Pair (Symbol "or", Pair (sexp,Nil)) -> tag_parser sexp
  | (*or*) Pair(Symbol ("or"),sexpressionList) -> Or((pairs_to_expr_list sexpressionList))
  | (*lambda simple no argumnets*) Pair(Symbol("lambda"), Pair(Nil, body)) ->
    LambdaSimple([], (sequence body))
  | (*lambda simple*) Pair(Symbol("lambda"), Pair(args, body)) when ((proper_list args) && (check_double_args args)) ->
    LambdaSimple((tag_proper_arguments args), (sequence body))
  | (*lamda variadic(opt)*) Pair(Symbol("lambda"), Pair(Symbol(vs), body)) -> LambdaOpt([], vs, (sequence body))
  | (*lambda opt*) Pair(Symbol("lambda"), Pair(args, body)) when (not (proper_list args) && (check_double_args args)) ->
    LambdaOpt((tag_improper_mandatory_arguments args), (get_optional_arg args), (sequence body))
  | (*Quasiquote*) Pair(Symbol ("quasiquote"), Pair(expression ,Nil)) -> (tag_parser (quasiquote_parse expression))
  | (*and*)Pair(Symbol "and", expression) -> (and_parser expression)
  |(*let*)Pair(Symbol("let"),letExpression) ->
    (let_parser letExpression)
  |(*let*_*)Pair(Symbol("let*"),let_star_exp) -> tag_parser (let_star_macro let_star_exp)
  |(*let_rec*)Pair(Symbol("letrec"),let_rec_exp) -> tag_parser (letrec_macro let_rec_exp)
  | (*cond*) Pair(Symbol("cond"), list_of_bodies) -> (cond_macro_expand list_of_bodies)
  |(*applic no args *) Pair(operator,Nil) -> Applic((tag_parser operator), [])
  | (*applic*) Pair(operator, expressionList) -> Applic((tag_parser operator), (pairs_to_expr_list expressionList))
  | _ -> raise X_syntax_error


and cond_macro_expand conds_and_bodies =
  match conds_and_bodies with
  | Pair(Pair(cond, Pair(Symbol("=>"), body)), Nil) ->
      tag_parser (Pair(Symbol("let"), Pair(Pair(Pair(Symbol("value"), Pair(cond, Nil)), Pair(Pair(Symbol("f"), Pair(Pair(Symbol("lambda"),
        Pair(Nil, body)), Nil)), Nil)), Pair(Pair(Symbol("if"), Pair(Symbol("value"), Pair(Pair(Pair(Symbol("f"), Nil), Pair(Symbol("value"), Nil)), Nil))), Nil))))
  | Pair(Pair(cond, Pair(Symbol("=>"), body)), rest_of_conds_and_bodies) ->
      tag_parser (Pair(Symbol("let"), Pair(Pair(Pair(Symbol("value"), Pair(cond, Nil)),
      Pair(Pair(Symbol("f"), Pair(Pair(Symbol("lambda"), Pair(Nil, body)), Nil)),
      Pair(Pair(Symbol("rest"), Pair(Pair(Symbol("lambda"),
      Pair(Nil, Pair(Pair(Symbol("cond"), rest_of_conds_and_bodies), Nil))), Nil)
      ), Nil))), Pair(Pair(Symbol("if"), Pair(Symbol("value"),
      Pair(Pair(Pair(Symbol("f"), Nil), Pair(Symbol("value"), Nil)), Pair(Pair(Symbol("rest"), Nil), Nil)))), Nil))))
  | Pair(Pair(Symbol("else"), body), Nil) -> (sequence body)
  | Pair(Pair(cond, body), Nil) -> If(tag_parser cond, sequence body, Const(Void))
  | Pair(Pair(cond, body), rest_of_conds_and_bodies) ->
                If(tag_parser cond, sequence body, cond_macro_expand rest_of_conds_and_bodies)
  | _ -> raise X_syntax_error


and define_tag_parser restOfDefineExpr =
  match restOfDefineExpr with
  (* both argsList and expression are pairs. *)
  | Pair(Pair(Symbol(name), argsList), expression) ->
    tag_parser (Pair(Symbol "define", Pair(Symbol(name), Pair(Pair(Symbol "lambda", Pair(argsList, expression)), Nil))))
  | Pair(defineVar, Pair(defineValue, Nil)) -> Def(tag_parser defineVar, tag_parser defineValue)
  | _-> raise X_syntax_error
(* takes sexprs pairs and outputs expr list *)

and pairs_to_expr_list pairs =
  match pairs with
  | Pair(x, Nil) -> (tag_parser x) :: []
  | Pair(car, cdr) -> (tag_parser car) :: (pairs_to_expr_list cdr)
  | _ -> raise X_syntax_error;

and sequence exprs =
  match exprs with
  | Pair(car, Nil) -> tag_parser car
  | Nil -> Const(Void)
  | _ -> Seq(pairs_to_expr_list exprs)



and check_double_args pairs =
  let rest_of_pairs = cdr pairs in
  let args = (try (pairs_to_expr_list pairs)
              with X_syntax_error -> (pairs_no_nil_to_expr_list pairs)) in
  let head = List.hd args in
  let rest_of_list = List.tl args in
  let double_list = List.filter (expr_eq head) rest_of_list in
  if ((List.length double_list) > 0)
  then false
  else (
    if (((List.length rest_of_list) == 1) || (List.length rest_of_list == 0))
    then true
    else (check_double_args rest_of_pairs)
  )
and pairs_no_nil_to_expr_list pairs =
  match pairs with
  | Pair(x, Pair(y, z)) -> (tag_parser x) :: (pairs_no_nil_to_expr_list (Pair(y, z)))
  | Pair(car, cdr) -> (tag_parser car) :: [(tag_parser cdr)]
  | _ -> raise X_syntax_error;


and and_parser expression =
  match expression with
  |Pair(car, Nil) -> (tag_parser car) (* #t is the unit elemnt of and *)
  |Nil -> Const(Sexpr(Bool(true))) (*#t by definition*)
  |Pair(car, expression) -> If((tag_parser car), (and_parser expression), Const(Sexpr(Bool(false))))
  (* if⟨expr1⟩(and⟨expr2⟩..... ⟨exprn⟩) #f *)
  |_-> raise X_syntax_error

and quasiquote_parse expression =
  match expression with
  |Pair(Symbol("unquote"),Pair(sexpr,Nil)) -> sexpr
  |Pair(Symbol("unquote-splicing"),Pair(sexpr,Nil)) -> raise X_syntax_error
  |Nil -> Pair(Symbol("quote"),Pair(Nil,Nil))
  |Symbol(a) -> Pair(Symbol ("quote"), Pair(Symbol(a), Nil))
  |Pair(Pair(Symbol ("unquote-splicing"),Pair(sexpr , Nil)),b) ->
    Pair(Symbol("append"),Pair(sexpr ,Pair((quasiquote_parse b),Nil)))
  |Pair(a,Pair(Symbol ("unquote-splicing"),Pair(sexpr,Nil)))->
    Pair(Symbol("cons"),Pair(quasiquote_parse a,Pair(sexpr,Nil)))
  |Pair(car, cdr) -> Pair(Symbol "cons", Pair(quasiquote_parse car, Pair(quasiquote_parse cdr, Nil)))
  |_ ->  expression

and sexprs_list_to_exprs_list lst =
  (List.map tag_parser lst)

(* in this method we will build a let by converting it into appplic, the operator will be lambda simple, with vars which
   we will extract from the 'bindings'. the args for the applic wiil be the exprs list which will be built from the vals in bindings. *)
and let_parser exp =
  match exp with
  | Pair(bindings, bodyOfLet) ->
    Applic(LambdaSimple((getBindingsVars bindings), (sequence bodyOfLet)), (sexprs_list_to_exprs_list (getBindingsVals bindings)))
  | _ -> raise X_syntax_error

and getBindingsVals bindings =
  match bindings with
  |Pair(Pair (x, Pair(y, Nil)), z) -> List.append [y] (getBindingsVals z)
  |_ -> []

and getBindingsVars bindings =
  match bindings with
  |Pair(Pair(Symbol(x), y), z) -> List.append [x] (getBindingsVars z)
  |_ -> []


and let_star_macro exp =
  match exp with
  (* 0 args *)
  |Pair(Nil,body_let) -> Pair(Symbol ("let"), Pair(Nil, body_let))
  (* 1 args *)
  |Pair(Pair(Pair(Symbol(x),Pair(value,Nil)),Nil),body_let) ->
    Pair(Symbol("let"),Pair(Pair(Pair(Symbol(x),Pair(value,Nil)),Nil),body_let))
  (* more than 1 args *)
  |Pair(Pair(Pair(Symbol(x), Pair(value, Nil)), rest_bindings), body_let) ->
    Pair(Symbol ("let"), Pair(Pair(Pair(Symbol(x), Pair(value, Nil)), Nil), Pair(Pair(Symbol ("let*"), Pair(rest_bindings, body_let)), Nil)))
  |_ -> raise X_syntax_error

and letrec_macro sexp =
  match sexp with
  |Pair(args, body) -> Pair(Symbol "let", Pair ((letrec_args args), (letrec_body args body)))
  |_ -> raise X_syntax_error

and letrec_args args =
  match args with
  |Pair(Pair(x, vals), rest) ->
    Pair(Pair(x, Pair(Pair(Symbol "quote", Pair(Symbol ("whatever"), Nil)), Nil)), (letrec_args rest))
  |_-> Nil

and letrec_body args body =
  match args with
  |Pair(Pair (x, args), rest) ->
    Pair(Pair(Symbol "set!", Pair(x, args)), (letrec_body rest body))
  |_-> body
;;

let my_tag sexp = tag_parser sexp;;

let my_tags sexpr = (List.map my_tag sexpr)

module Tag_Parser : TAG_PARSER = struct


let tag_parse_expression sexpr = tag_parser sexpr;;

let tag_parse_expressions sexpr = (List.map tag_parse_expression sexpr);;


end;; (* struct Tag_Parser *)
