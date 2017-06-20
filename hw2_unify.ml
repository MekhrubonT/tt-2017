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
	

exception NoSolution;;
	

exception Error;;
		
(* Checks if alg term contains var *)
let rec contains_var var alg = match alg with
	Var v -> var = v
	| Fun (name, ls) -> List.exists (contains_var var) ls;;
	

let rec print_term term = match term with 
	Var a -> print_string (a^" ")
	| Fun(name, ls) -> print_string (name ^ "(");
						List.iter print_term ls; 
						print_string ") ";;

let apply_substitution_to_sol sub sol = 
	List.map (fun(a, b) -> ((*print_string a;
						print_string "\n";
							print_term b;
						print_string "\n";
						print_term (apply_substitution sub b);
						print_string "\n";
						print_string "\n";*)
	(a, apply_substitution sub b))) sol;;
						
let rec zamykanie ls sol = match ls with 
	[] -> sol
	| (var, d)::tail -> 
(*		print_string ("var:"^var^"=");
		print_term d;
		print_string "\n";*)
				
	zamykanie (apply_substitution_to_sol ((var, d)::sol) tail)
					((var, d)::sol);;
							

let rec solve ls prefix = match ls with
	[] -> zamykanie (prefix) [] 
	| (Fun (ln, ll), Fun (rn, rl))::tail -> 
		if ln = rn then 
			solve (List.append (List.map2 (fun a b -> (a, b)) ll rl) tail) prefix
		else
			raise NoSolution
	| (Fun (n, l), Var v)::tail -> solve ((Var v, Fun (n, l))::tail) prefix 
	| (Var var, r)::tail -> if equals (Var var) r then solve tail prefix 
						else if contains_var var r then raise NoSolution
						else solve 
							(List.map (fun(a, b) -> (apply_substitution [var, r] a,
									apply_substitution [var, r] b)) tail)
							((var, r)::prefix);;

let solve_system equations = try Some (solve equations []) with _ -> None;;

let checker system = 
	List.iter (fun (lhs, rhs) -> print_term(lhs); print_string ("="); print_term rhs; print_string "\n") system;
	print_string "\n";

	match solve_system system with 
	None -> print_string "none\n";
	| Some ls -> 
		print_string "ok\n";
		List.iter (fun (name, term) -> print_string (name^"="); print_term term; print_string "\n") ls;
		print_string "----------\n";;


		

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
		

let sys0 = [(Var "a", Var "b"); (Var "x", Var "y")];;
let sys1 = [(Fun("f",[Var "a"]), Fun("f",[Fun("g",[Fun("h",[Var "b"])])])); (Var "a", Var "b")];;
let sys2 = [(Fun("f",[Var "a"]), Var "b")];;
let sys3 = [Fun("f",[Var "a"; Var "b"]), Fun("f",[Var "x"; Var "y"])];;
let sys4 = [Fun("f",[Var "a"; Var "b"]), Fun("g",[Var "x"; Var "y"])];;
let sys5 = [Fun("f",[Var "a"; Var "b"]), Fun("f",[Var "x"; Var "y"; Var "z"])];;
let sys6 = [(Var "a", Fun("f", [Var "a"]))];;
let sys7 = [(Var "a", Var "a")];;
List.iter checker [sys0;sys1;sys2;sys3;sys4;sys5;sys6;sys7];;
checker sys7;;

