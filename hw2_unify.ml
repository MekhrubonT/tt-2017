type algebraic_term = Var of string | Fun of string * (algebraic_term list)


let rec concat_func_names_in_algeb_term x = match x with
	Var y -> y
	| Fun (name, ls) -> List.fold_left (fun f s -> f ^ concat_func_names_in_algeb_term s) name ls;;

let rec concat_all_functions_names_in_list x = match x with
	[] -> "end"
	| (fs, sn)::tl -> (concat_func_names_in_algeb_term fs) ^ (concat_func_names_in_algeb_term sn) 
						^ (concat_all_functions_names_in_list tl);;

let system_to_equation x = let func_concats = concat_all_functions_names_in_list x in		
							(Fun (func_concats, List.map fst x), Fun (func_concats, List.map snd x));;
						

let rec apply_substitution x y = match y with
	Var v -> (try let (pf, ps) = List.find (fun (f, s) -> f = v) x in 
				ps with _ -> Var v)
	| Fun (f, data) -> Fun (f, (List.map (fun term -> apply_substitution x term) data));;


exception Key_not_found of string;;

let rec check_to_lists predicate list1 list2 = (List.length list1) = List.length list2 
		&& List.fold_left2 (fun pr b c -> pr && predicate b c) true list1 list2;;
	
let rec equals t1 t2 = match (t1, t2) with 
	(Var a, Var b) -> a = b
	| (Fun (a, la), Fun (b, lb)) -> a = b && check_to_lists equals la lb
	| _ -> false;;

	
let rec get_subst subst_list var = match subst_list with 
	[] -> Var var
	| (name, s)::tl -> if name = var then s else get_subst tl var;;
	
let rec substitute_term sol term = match term with 
	Var a -> get_subst sol a
	| Fun (name, ls) -> Fun (name, List.map (substitute_term sol) ls);;
	
let rec check_equation_solution sol fs sn = match (fs, sn) with
	(Fun (nl, lil), Fun(nr, lir)) -> nl = nr && check_to_lists (check_equation_solution sol) lil lir
	| (a, b) -> equals (substitute_term sol a) (substitute_term sol b);;
		
let rec check_solution x y = match y with 
	[] -> true 
	| (fs, sn)::tl -> check_equation_solution x fs sn && check_solution x tl;;

let rec transform1 x = match x with 
	[] -> []
	| (Fun (name, ls), Var a)::tail -> (Var a, Fun (name, ls))::(transform1 tail)
	| hd::tail -> hd::(transform1 tail);;

let rec transform2 ls = match ls with
	[] -> []
	| (fs, sn)::tail -> if equals fs sn then transform2 tail else (fs, sn)::(transform2 tail);;

exception NoSolution;;
	
let rec transform3 ls = match ls with
	[] -> []
	| (Fun (ln, ll), Fun (rn, rl))::tail -> if ln = rn 
		then List.append (transform2 (transform1 (List.map2 (fun a b -> (a, b)) ll rl))) (transform3 tail)
			else raise NoSolution
	| hd::tail -> hd::(transform3 tail);;

exception Error;;
	
let matcher x = match x with
	(Var a, y) -> (a, y)
	| _ -> raise Error;;

let rec substterm prev nw term = match term with 
	Var a -> if a = prev then Var nw else Var a
	| Fun (name, data) -> Fun (name, List.map (fun t1 -> substterm prev nw t1) data);;
	
let rec subst prev nw ls = List.map (fun (t1, t2) -> (substterm prev nw t1, substterm prev nw t2)) ls;;

	
let rec find_varvar cur pref = match cur with 
	[] -> raise Error
	| (Var a, Var b)::tail -> (Var a, Var b)::(solve (subst a b (List.append pref tail)))
	| hd::tail -> find_varvar tail (hd::pref)
and transform4 ls fs sn = match ls with
	[] -> if sn = [] then fs else 
			let fss = List.map matcher fs in
			solve (List.map (fun (a, b) -> (substitute_term fss a, substitute_term fss b)) sn)
	| (Var a, Fun (name, fargs))::tail -> if List.exists (fun term -> equals (Var a) term) fargs then raise NoSolution 
						else transform4 tail ((Var a, Fun (name, fargs))::fs) sn
	| hd::tail -> transform4 tail fs (hd::sn)

and solve x = let cur_state = (transform3 (transform2 (transform1 x))) in
				try find_varvar cur_state [] with _ -> transform4 cur_state [] [];;
				
let rec make_subst sbs term = match term with 
	Var a -> (try let (l, r) = List.find (fun (lh, rh) -> equals lh (Var a)) sbs in 
					make_subst sbs r
					with _ -> Var a)
	| Fun (name, terms) -> Fun(name, List.map (make_subst sbs) terms);;

let zamyk ls = List.map (fun (l, r) -> (l, make_subst ls r)) ls;;
				
let solve_system equations = try Some (List.map matcher (zamyk (solve equations))) with _ -> None;;



let rec print_term term = match term with 
	Var a -> print_string (a^" ")
	| Fun(name, ls) -> print_string (name ^ "(");
						List.iter print_term ls; 
						print_string ") ";;
let isys1 = [Fun("f",[Var "y"; Fun("h",[Var "x"; Var "y"])]), Fun("f",[Fun("g",[Var "a"; Var "b"]); Fun("h", [Var "x"; Var "x"])]); Fun("h",[Var "x"; Var "y"]), Fun("h", [Var "a"; Var "a"])];;
let my_test = [(Var "a", Var "b"); (Var "a", Var "c"); (Var "b", Fun ("f", [Var "x"]))];;

let at4 = Fun("f",[Var "x"]);;
let at8 = Fun("f",[Var "x"; Var "y"]);;

let sys0 = [(Var "a", Var "b"); (Var "a", Var "c"); (Var "b", Var "d")];;
		
List.iter (fun (lhs, rhs) -> print_term(lhs); print_string ("="); print_term rhs; print_string "\n") sys0;;
print_string "\n";;
						
match solve_system sys0 with 
	None -> print_string "none"
	| Some ls -> 
		
		List.iter (fun (name, term) -> print_string (name^"="); print_term term; print_string "\n") ls;;