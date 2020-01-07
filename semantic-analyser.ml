#use "tag-parser.ml";;

type var = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | Const' of constant
  | Var' of var
  | Box' of var
  | BoxGet' of var
  | BoxSet' of var * expr'
  | If' of expr' * expr' * expr'
  | Seq' of expr' list
  | Set' of expr' * expr'
  | Def' of expr' * expr'
  | Or' of expr' list
  | LambdaSimple' of string list * expr'
  | LambdaOpt' of string list * string * expr'
  | Applic' of expr' * (expr' list)
  | ApplicTP' of expr' * (expr' list);;

let rec expr'_eq e1 e2 =
  match e1, e2 with
  | Const' Void, Const' Void -> true
  | Const'(Sexpr s1), Const'(Sexpr s2) -> sexpr_eq s1 s2
  | Var'(VarFree v1), Var'(VarFree v2) -> String.equal v1 v2
  | Var'(VarParam (v1,mn1)), Var'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | Var'(VarBound (v1,mj1,mn1)), Var'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | If'(t1, th1, el1), If'(t2, th2, el2) -> (expr'_eq t1 t2) &&
                                            (expr'_eq th1 th2) &&
                                              (expr'_eq el1 el2)
  | (Seq'(l1), Seq'(l2)
  | Or'(l1), Or'(l2)) -> List.for_all2 expr'_eq l1 l2
  | (Set'(var1, val1), Set'(var2, val2)
  | Def'(var1, val1), Def'(var2, val2)) -> (expr'_eq var1 var2) &&
                                             (expr'_eq val1 val2)
  | LambdaSimple'(vars1, body1), LambdaSimple'(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr'_eq body1 body2)
  | LambdaOpt'(vars1, var1, body1), LambdaOpt'(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr'_eq body1 body2)
  | Applic'(e1, args1), Applic'(e2, args2)
  | ApplicTP'(e1, args1), ApplicTP'(e2, args2) ->
	 (expr'_eq e1 e2) &&
	   (List.for_all2 expr'_eq args1 args2)
  | _ -> false;;
	
                       
exception X_syntax_error;;

let rec find_index_in_list name lst j =
  match lst with
  | [] -> -1
  | car::cdr -> (if car = name
                   then j
                   else (find_index_in_list name cdr (j+1)))

let rec find_lex_address var_name env j =
  match env with
  | [] -> (-1, -1)
  | car :: cdr -> (if (List.mem var_name car)
                   then (j, (find_index_in_list var_name car 0))
                   else (find_lex_address var_name cdr (j+1)))



let rec lexical_addresses env params after_first expr =
  match expr with
  | Const(sexp) -> Const'(sexp)
  | Var(var_name) -> (if (List.mem var_name params)
                      then Var'(VarParam(var_name, find_index_in_list var_name params 0))
                      else
                        (let opt_address = find_lex_address var_name env 0 in
                        match opt_address with
                        | (-1, -1) -> (Var'(VarFree(var_name)))
                        | (outer_index, inner_index) -> Var'(VarBound(var_name, outer_index, inner_index))))
  | If(test, dit, dif) -> If'((lexical_addresses env params after_first test), (lexical_addresses env params after_first dit), (lexical_addresses env params after_first dif))
  | Seq(exprs) -> Seq'(List.map (lexical_addresses env params after_first) exprs)
  | Set(set_var, set_value) -> Set'((lexical_addresses env params after_first set_var), (lexical_addresses env params after_first set_value))
  | Def(def_name, def_val) -> Def'((lexical_addresses env params after_first def_name), (lexical_addresses env params after_first def_val))
  | Or(exprs) -> Or'(List.map (lexical_addresses env params after_first) exprs)
  | LambdaSimple(new_params, body) -> (if params = []
                                       then (if after_first
                                             then LambdaSimple'(new_params, (lexical_addresses (List.append [params] env) new_params true body))
                                             else LambdaSimple'(new_params, (lexical_addresses env new_params true body)))
                                       else LambdaSimple'(new_params, (lexical_addresses (List.append [params] env) new_params true body)))
  | LambdaOpt(new_params, opt_param, body) -> (let new_all_params = List.append new_params [opt_param] in
                                               if params = []
                                               then (if after_first
                                                     then LambdaOpt'(new_params, opt_param, (lexical_addresses (List.append [params] env) new_all_params true body))
                                                     else LambdaOpt'(new_params, opt_param, (lexical_addresses env new_all_params true body)))
                                               else LambdaOpt'(new_params, opt_param, (lexical_addresses (List.append [params] env) new_all_params true body)))
  | Applic(operator, args) -> Applic'((lexical_addresses env params after_first operator), (List.map (lexical_addresses env params after_first) args))


let rec tail_calls in_tp expr =
  match expr with
  | Const'(exp) -> Const'(exp)
  | Var'(var) -> Var'(var)
  | Box'(var) -> Box'(var)
  | BoxGet'(var) -> BoxGet'(var)
  | BoxSet'(var, expr) -> BoxSet'(var, (tail_calls in_tp expr))
  | If'(test, dit, dif) -> If'((tail_calls false test), (tail_calls in_tp dit), (tail_calls in_tp  dif))
  | Seq'(exprs) -> (let rev_list = List.rev exprs in
                    let last = List.hd rev_list in
                    let rest = List.rev (List.tl rev_list) in
                    Seq'(List.append (List.map (tail_calls false) rest) [tail_calls true last]))
  | Set'(set_var, set_value) -> Set'((tail_calls false set_var), (tail_calls false set_value))
  | Def'(def_name, def_value) -> Def'((tail_calls false def_name), (tail_calls false def_value))
  | Or'(exprs) -> (let rev_list = List.rev exprs in
                   let last = List.hd rev_list in
                   let rest = List.rev (List.tl rev_list) in
                   Or'(List.append (List.map (tail_calls false) rest) [tail_calls true last]))
  | LambdaSimple'(params, body) -> LambdaSimple'(params, (tail_calls true body))
  | LambdaOpt'(params, opt_param, body) -> LambdaOpt'(params, opt_param, (tail_calls true body))
  | Applic'(operator, args) -> (if in_tp
                                then ApplicTP'((tail_calls false operator), (List.map (tail_calls false) args))
                                else Applic'((tail_calls false operator), (List.map (tail_calls false) args)))
  | ApplicTP'(operator, args) -> ApplicTP'((tail_calls false operator), (List.map (tail_calls false) args))



let check = fun a b -> a || b

let is_boxing read_list write_list =
  let check_writes num =
    let remaining = List.filter (fun number -> number != num) write_list in
    ((List.length remaining) > 0) in
  let lst = List.map (check_writes) read_list in
  List.fold_right check lst false;;


let rec boxing expr =
  match expr with
  | Const'(exp) -> Const'(exp)
  | Var'(var) -> Var'(var)
  | Box'(var) -> Box'(var)
  | BoxGet'(var) -> BoxGet'(var)
  | BoxSet'(var, exp) -> BoxSet'(var, (boxing exp))
  | If'(test, dit, dif) -> If'((boxing test), (boxing dit), (boxing dif))
  | Seq'(exps) -> Seq'(List.map boxing exps)
  | Set'(set_var, set_val) -> Set'((boxing set_var), (boxing set_val))
  | Def'(def_var, def_val) -> Def'((boxing def_var), (boxing def_val))
  | Or'(exps) -> Or'(List.map boxing exps)
  | LambdaSimple'(params, body) -> LambdaSimple'(params, (boxing (handle_lambda (List.rev params) body ((List.length params) - 1))))
  | LambdaOpt'(params, opt_param, body) -> LambdaOpt'(params, opt_param, (boxing (handle_lambda (List.rev (List.append params [opt_param])) body ((List.length params) - 1))))
  | Applic'(operator, args) -> Applic'((boxing operator), (List.map boxing args))
  | ApplicTP'(operator, args) -> ApplicTP'((boxing operator), (List.map boxing args));


and handle_lambda params body index =
  match params with
  | param :: rest -> handle_lambda rest (check_box_var param body index) (index - 1)
  | [] -> body;


and check_box_var param body param_minor =
  let global_reads = ref [] in
  let global_writes = ref [] in
  let add_to_reads branch_num =
    (if (not (List.mem branch_num !global_reads))
    then global_reads := List.append !global_reads [branch_num]) in
  let add_to_writes branch_num =
    (if (not (List.mem branch_num !global_writes))
    then global_writes := List.append !global_writes [branch_num]) in

  let remove_dont_care dont_care expr =
    expr in

  let rec check_branch param branch_num expr' =
    (match expr' with
    | Const'(exp) -> Const'(exp)
    | Var'(var) -> (match var with
                    | VarBound(name, major, minor) when name = param -> (let dont_care = add_to_reads branch_num in
                                                                        remove_dont_care dont_care (Var'(var)))
                    | VarParam(name, index) when name = param -> (let dont_care = add_to_reads branch_num in
                                                                        remove_dont_care dont_care (Var'(var)))
                    | _ -> Var'(var))
    | Box'(var) -> Box'(var)
    | BoxGet'(var) -> BoxGet'(var)
    | BoxSet'(var, exp) -> BoxSet'(var, (check_branch param branch_num exp))
    | If'(test, dit, dif) -> If'((check_branch param branch_num test), (check_branch param branch_num dit), (check_branch param branch_num dif))
    | Seq'(exps) -> Seq'(List.map (check_branch param branch_num) exps)
    | Set'(set_var, set_val) -> (match set_var with
                                | Var'(VarBound(name, major, minor)) when name = param -> (let dont_care = add_to_writes branch_num in
                                                                                           remove_dont_care dont_care (Set'(set_var, (check_branch param branch_num set_val))))
                                | _ -> Set'((check_branch param branch_num set_var), (check_branch param branch_num set_val)))
    | Def'(def_var, def_val) -> Def'((check_branch param branch_num def_var), (check_branch param branch_num def_val))
    | Or'(exps) -> Or'(List.map (check_branch param branch_num) exps)
    | LambdaSimple'(params, body) -> (if (List.mem param params)
                                      then LambdaSimple'(params, body)
                                      else LambdaSimple'(params, (check_branch param branch_num body)))
    | LambdaOpt'(params, opt_param, body) -> (if (List.mem param (List.append params [opt_param]))
                                              then LambdaOpt'(params, opt_param, body)
                                              else LambdaOpt'(params, opt_param, (check_branch param branch_num body)))
    | Applic'(operator, args) -> Applic'((check_branch param branch_num operator), (List.map (check_branch param branch_num) args))
    | ApplicTP'(operator, args) -> ApplicTP'((check_branch param branch_num operator), (List.map (check_branch param branch_num) args))) in

  let help_func expr =
    (let next_num = Random.int 9999999 in
    check_branch param next_num expr) in

  let main_branch = (Random.int 9999999) in

  let rec box_param param body =
    (match body with
    | Const'(exp) -> Const'(exp)
    | Var'(var) -> (match var with
                    | VarParam(name, _) when name = param -> BoxGet'(var)
                    | VarBound(name, _, _) when name = param -> BoxGet'(var)
                    | _ -> Var'(var))
    | Box'(var) -> Box'(var)
    | BoxGet'(var) -> BoxGet'(var)
    | BoxSet'(var, exp) -> BoxSet'(var, (box_param param exp))
    | If'(test, dit, dif) -> If'((box_param param test), (box_param param dit), (box_param param dif))
    | Seq'(exps) -> Seq'(List.map (box_param param) exps)
    | Set'(set_var, set_val) -> (match set_var with
                                | Var'(VarParam(name, minor)) when name = param -> BoxSet'(VarParam(name, minor), (box_param param set_val))
                                | Var'(VarBound(name, major, minor)) when name = param -> BoxSet'(VarBound(name, major, minor), (box_param param set_val))
                                | _ -> Set'((box_param param set_var), (box_param param set_val)))
    | Def'(def_var, def_val) -> Def'((box_param param def_var), (box_param param def_val))
    | Or'(exps) -> Or'(List.map (box_param param) exps)
    | LambdaSimple'(params, body) -> (if (List.mem param params)
                                     then LambdaSimple'(params, body)
                                     else LambdaSimple'(params, (box_param param body)))
    | LambdaOpt'(params, opt_param, body) -> (if (List.mem param (List.append params [opt_param]))
                                     then LambdaOpt'(params, opt_param, body)
                                     else LambdaOpt'(params, opt_param, (box_param param body)))
    | Applic'(operator, args) -> Applic'((box_param param operator), (List.map (box_param param) args))
    | ApplicTP'(operator, args) -> ApplicTP'((box_param param operator), (List.map (box_param param) args))) in

  let add_boxing_of_param_at_beggining body =
    (match body with
    | Seq'(Set'(Var'(VarParam(name1, index1)), Box'(VarParam(name2, index2))) :: exps) when (name1 = name2) ->
      (Seq'(List.append [Set'(Var'(VarParam(param, param_minor)), Box'(VarParam(param, param_minor)));
                        Set'(Var'(VarParam(name1, index1)), Box'(VarParam(name2, index2)))] exps))
    | Seq'(exps) -> Seq'([Set'(Var'(VarParam(param, param_minor)), Box'(VarParam(param, param_minor))); body])
    | _ -> Seq'(List.append [Set'(Var'(VarParam(param, param_minor)), Box'(VarParam(param, param_minor)))] [body])) in

  let rec main_func body =
    (match body with
    | Const'(exp) -> Const'(exp)
    | Var'(var) -> check_branch param main_branch (Var'(var))
    | Box'(var) -> Box'(var)
    | BoxGet'(var) -> BoxGet'(var)
    | BoxSet'(var, exp) -> BoxSet'(var, (main_func exp))
    | If'(test, dit, dif) -> If'((main_func test), (main_func dit), (main_func dif))
    | Seq'(exps) -> Seq'(List.map main_func exps)
    | Set'(set_var, set_val) -> (match set_var with
                                | Var'(VarParam(name, _)) when name = param -> (let dont_care = add_to_writes main_branch in
                                                                                remove_dont_care dont_care (Set'((set_var), (main_func set_val))))
                                | _ -> Set'((main_func set_var), (main_func set_val)))
    | Def'(def_var, def_val) -> Def'((main_func def_var), (main_func def_val))
    | Or'(exps) -> Or'(List.map main_func exps)
    | LambdaSimple'(params, body) -> help_func (LambdaSimple'(params, body))
    | LambdaOpt'(params, opt_param, body) -> help_func (LambdaOpt'(params, opt_param, body))
    | Applic'(operator, args) -> Applic'((main_func operator), (List.map main_func args))
    | ApplicTP'(operator, args) -> ApplicTP'((main_func operator), (List.map main_func args))) in

  let ret = main_func body in
  if (is_boxing !global_reads !global_writes)
  then (let boxed_lambda = (box_param param ret) in
        (add_boxing_of_param_at_beggining boxed_lambda))
  else ret;;

let my_run e = boxing (tail_calls false (lexical_addresses [] [] false e));;

let my_runs exprs = List.map my_run exprs;;

module type SEMANTICS = sig
  val run_semantics : expr -> expr'
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
end;;

module Semantics : SEMANTICS = struct

let annotate_lexical_addresses e = lexical_addresses [] [] false e;;

let annotate_tail_calls e = tail_calls false e;;

let box_set e = boxing e;;

let run_semantics expr =
  box_set
    (annotate_tail_calls
       (annotate_lexical_addresses expr));;
  
end;; (* struct Semantics *)
