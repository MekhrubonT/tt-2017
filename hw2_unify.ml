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

		
let rec check_equation_solution sol fs sn = match (fs, sn) with
	(Fun (nl, lil), Fun(nr, lir)) -> nl = nr && check_to_lists (check_equation_solution sol) lil lir
	| (a, b) -> equals (apply_substitution sol a) (apply_substitution sol b);;
		
let rec check_solution x y = match y with 
	[] -> true 
	| (fs, sn)::tl -> check_equation_solution x fs sn && check_solution x tl;;
	
(* Swap if lhs = fun and rhs = var *)
let rec transform1 x = match x with 
	[] -> []
	| (Fun (name, ls), Var a)::tail -> (Var a, Fun (name, ls))::(transform1 tail)
	| hd::tail -> hd::(transform1 tail);;

(* Remove if lhs=rhs *)
let rec transform2 ls = match ls with
	[] -> []
	| (fs, sn)::tail -> if equals fs sn then transform2 tail else (fs, sn)::(transform2 tail);;

exception NoSolution;;
	
(* Simplify fun = fun *)
let rec transform3 ls = match ls with
	[] -> []
	| (Fun (ln, ll), Fun (rn, rl))::tail -> 
		if ln = rn 
		then transform3 (List.append (transform2 (transform1 (List.map2 (fun a b -> (a, b)) ll rl))) tail)
			else 
				raise NoSolution
	| hd::tail -> hd::(transform3 tail);;

exception Error;;
	
let matcher x = match x with
	(Var a, y) -> (a, y)
	| _ -> raise Error;;
	
(* Checks if alg term contains var *)
let rec contains_var var alg = match alg with
	Var v -> var = v
	| Fun (name, ls) -> List.exists (contains_var var) ls;;
	

let rec print_term term = match term with 
	Var a -> print_string (a^" ")
	| Fun(name, ls) -> print_string (name ^ "(");
						List.iter print_term ls; 
						print_string ") ";;

						
let rec transform4 ls prefix = match ls with
	[] -> List.map matcher prefix 
	| (Var var, r)::tail -> 
			(match r with 
					Fun (name, ls) -> 
							if List.exists (equals (Var var)) ls then raise NoSolution
					| _ -> ());
			let oth = List.append prefix tail in 
			if List.exists (fun (a, b) -> (contains_var var a) || (contains_var var b)) oth then
				solve ((Var var, r)::
				(List.map (fun(a, b) -> (apply_substitution [var, r] a,
										apply_substitution [var, r] b)) oth))
			else 
				transform4 tail ((Var var, r)::prefix)			
					
	| hd::tail -> transform4 tail (hd::prefix)	
	
and solve x = let q = (transform3 (transform2 (transform1 x))) in 
		
				transform4 q []
				;;
								
let solve_system equations = try Some (solve equations) with _ -> None;;



let isys1 = [Fun("f",[Var "y"; Fun("h",[Var "x"; Var "y"])]), Fun("f",[Fun("g",[Var "a"; Var "b"]); Fun("h", [Var "x"; Var "x"])]); Fun("h",[Var "x"; Var "y"]), Fun("h", [Var "a"; Var "a"])];;
let my_test = [(Var "a", Var "b"); (Var "a", Var "c"); (Var "b", Fun ("f", [Var "x"]))];;

let at4 = Fun("f",[Var "x"]);;
let at8 = Fun("f",[Var "x"; Var "y"]);;

let left = Fun("a", [Fun("b", [Var "a"; Var"b"])]);;
let right = Fun("a", [Fun("b", [Var "q"; Var"b"])]);;

let sys0 = [(left, right)];;


let sys1 = [(Var "m1", Fun("ar", [Var "m2"; Var "m3"]));
				(Var "m1", Fun("ar", [Var "m3"; Var "m4"]))];;

let system = sys0;;
		
List.iter (fun (lhs, rhs) -> print_term(lhs); print_string ("="); print_term rhs; print_string "\n") system;;
print_string "\n";;

match solve_system system with 
	None -> print_string "none\n";
	| Some ls -> 
		print_string "ok\n";
		List.iter (fun (name, term) -> print_string (name^"="); print_term term; print_string "\n") ls;;