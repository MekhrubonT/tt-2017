open Hw1

type simp_type = S_Elem of string | S_Arrow of simp_type * simp_type


type hm_lambda = HM_Var of string | HM_Abs of string * hm_lambda | HM_App of hm_lambda * hm_lambda | HM_Let of string * hm_lambda * hm_lambda
type hm_type = HM_Elem of string | HM_Arrow of hm_type * hm_type | HM_ForAll of string * hm_type

module MAP = Map.Make(String);;
module SET = Set.Make(String);;




(* string of hindley milner type *)
let rec string_of_hmt hmt = 
		match hmt with
                        HM_Elem v -> v
                        | HM_Arrow(hmt1, hmt2) -> "(" ^ (string_of_hmt hmt1) ^ " -> " ^ (string_of_hmt hmt2) ^ ")" 
                        | HM_ForAll(v, hmt) -> "∀" ^ v ^ "." ^ (string_of_hmt hmt);;


(* string of hindley milner lambda ie term *)
let rec string_of_hml hml =
	match hml with 
		HM_Var v -> v
		| HM_Abs(v, hml) -> ("\\" ^ v ^ "." ^ "(" ^ (string_of_hml hml) ^ ")")
		| HM_App(hml1, hml2) -> ("(" ^ (string_of_hml hml1) ^ " " ^ (string_of_hml hml2) ^ ")")
		| HM_Let(v, hml1, hml2) -> ("let " ^ v ^ " = (" ^ (string_of_hml hml1) ^ ") in (" ^ (string_of_hml hml2)) ^ ")";;

		(* Function is almost fully copypasted from Hw1 module,
	where we were parsing primitive lambdas from string.
	To get rid of copying the one should probably
	use generic typic or templates and I'm 
	not ready to do it yet 

	This function is implemented only because of 
	enthusiasm and just for fun. It is not 
	homework. As a result it is prohibited to
	start variable names with "i" or with "l" in
	strings passed to this function (for easier "let .. in .." parsing)
	
	Consider yourself warned *)

let hml_of_string s =
	let s = s ^ ";" in
	let pos = ref 0 in (*pos points to first not processed element*)
	let get () = s.[!pos] in (*returns next not processed element*)
	let next () = if !pos < String.length s - 1 then pos := !pos + 1 in (*increment pos*)
	let eat x = if get () = x then next () else failwith "Incorrect input string" in
	let is_end () = if (get ()) = ';' then true else false in		
		
	(* Function reads the name from current position till next space or dot *)
	(* unit -> string *)
	let parse_name_str () =
		let rec impl s =
			if (get ()) <> ' ' && (get ()) <> '.' && (get ()) <> ')' && not (is_end ())  
				then let c = get() in next(); impl (s ^ String.make 1 c)
				else s in
		impl "" in	

	(* unit -> hml *)
	let parse_name () = 
		HM_Var(parse_name_str ()) in

	(* unit -> hml *)
	let rec parse_hml () =
		let ans = 	
			match (get ()) with 
				'\\' -> parse_abs ()
				| '(' -> (eat '('; let ret = parse_hml () in eat ')'; ret)
				| 'l' -> parse_let () (* todo fix for vars starting with l *)
				| _ ->  parse_name () in
		if_is_app ans 

	and parse_let () =
		eat 'l'; eat 'e'; eat 't'; eat ' ';
		let v = parse_name_str () in
		eat ' '; eat '='; eat ' ';
		let hml1 = parse_hml () in
		eat 'i'; eat 'n'; eat ' '; (* space before in is read by app *)
		let hml2 = parse_hml () in
		HM_Let(v, hml1, hml2) 

	(* unit -> lambda *)
	and parse_abs () = 
		eat '\\';
		let name = parse_name_str () in
		eat '.';
		HM_Abs(name, parse_hml ())

	(* function checks if expression continues and makes app left associative *)
	(* lambda -> lambda *)	
	and if_is_app prev = 
		if (is_end () || s.[!pos] = ')' || s.[!pos] = 'i') then prev else 
			(eat ' '; 
			(* if we encounter 'i' after space, than it is beginning of "in", no app here *)
			if (get ()) = 'i' then prev else
				if_is_app (HM_App(prev, 
					match (get ()) with 
						'\\' -> parse_abs () 
						| '(' -> (eat '('; let ans = parse_hml () in	eat ')'; ans)
						| 'l' -> parse_let () 
						| _ -> parse_name ()))) in

	parse_hml ();; 

		
print_string "\n\n\n\nHW4\n";;

let type_counter = ref 0;;
let gen() = type_counter := !type_counter + 1;
			"m"^(string_of_int !type_counter);;

exception NotSimpleType;;

let a_elem t = Hw2_unify.Var t;;
let a_arrow l r = Hw2_unify.Fun ("arrow", [l; r]);;

let rec alg_to_simp alg = match alg with
	Hw2_unify.Var var -> S_Elem var 
	| Hw2_unify.Fun ("arrow", [l; r]) -> S_Arrow (alg_to_simp l, alg_to_simp r)
	| _ -> raise NotSimpleType;;

let rec st_to_string st = 
        match st with 
                S_Elem v -> v
                | S_Arrow (x, y) -> "(" ^ (st_to_string x) ^ " -> " ^
                (st_to_string y) ^ ")";;

let alg_to_str x = st_to_string (alg_to_simp x);;

	
let rec infer_simp_type_helper m var_types = match m with
	Var var -> ([], MAP.find var var_types)
	| Abs (var, t) -> 
					let name = (gen()) in
					let temp = MAP.add var (a_elem name) var_types in
					print_string (var^" type is "^name^"\n");
					let (ep, tp) = infer_simp_type_helper t temp in 
						(ep, a_arrow (MAP.find var temp) tp)
	| App (p, r) -> let ep, tp = infer_simp_type_helper p var_types in
					let er, tr = infer_simp_type_helper r var_types in
					let pi = a_elem (gen()) in
					print_string ("app "^(alg_to_str tp)^"\t"^(alg_to_str tr)^"\t"^(alg_to_str pi)^"\n");
					((tp, a_arrow tr pi)::(List.append ep er), pi);;

let init_free_vars_types lmb = let fv = Hw1_reduction.free_vars lmb in
							List.fold_left (fun mp var -> MAP.add var (a_elem (gen())) mp) MAP.empty fv;;
					
				
let infer_simp_type lmb = let system, tp = infer_simp_type_helper lmb (init_free_vars_types lmb) in 
	print_string ("type_t="^(st_to_string (alg_to_simp tp))^"\n");
	print_string "system\n";
	List.iter (fun (a, b) -> print_string ((alg_to_str a)^"="^(alg_to_str b)^"\n")) system;
	print_string "end\n";
							match Hw2_unify.solve_system system with 
							None -> None
							| Some ls -> Some (List.map (fun (a, b) -> (a, alg_to_simp b)) ls, 
							alg_to_simp (Hw2_unify.apply_substitution ls tp));;

let l1 = Hw1.lambda_of_string("\\x. x \\x. x");;

let func x = 
			
			let ans = infer_simp_type x in
			match ans with 
				None -> print_string "No type\n"
				| Some (ls, tp) -> print_string ((st_to_string tp)^"\n");;

List.iter func [l1];;



print_string "\n\n\n\nW\n";;

let rec hmt_to_string hm = 
        match hm with 
                HM_Elem v -> v
                | HM_Arrow (lhs, rhs) -> "("^(hmt_to_string lhs)^"->"^(hmt_to_string rhs)^")"
				| HM_ForAll (var, rhs) -> "V "^var^"."^(hmt_to_string rhs);;

let rec hmv_to_string hm = 
        match hm with 
                HM_Var v -> v	
                | HM_Abs (var, t) -> "\\"^var^"."^(hmv_to_string t)
				| HM_App (lhs, rhs) -> "("^(hmv_to_string lhs)^") ("^(hmv_to_string rhs)^")"
				| HM_Let (var, lhs, rhs) -> "let " ^ var ^ "=" ^ (hmv_to_string lhs) ^ " in "^ (hmv_to_string rhs);;
			
			
exception NoTypeExists;;

(* Apply substitutions to type tp except variables listed in blocked *)
(* HM_type -> Map -> Set -> HM_type *)
let rec rename tp substitutions blocked = match tp with
	HM_Elem v -> if (MAP.mem v substitutions) = true && (SET.mem v blocked) = false then 
							MAP.find v substitutions
							else tp
	| HM_Arrow (lhs, rhs) -> HM_Arrow(rename lhs substitutions blocked, 
										rename rhs substitutions blocked)
	| HM_ForAll (name, er) -> HM_ForAll(name, rename er substitutions (SET.add name blocked));;

	
(* Generate new names for inner HM_ForAll variables and rename them *)
let rec crt_and_rename_vars tp map = match tp with 
	HM_ForAll (name, inner) -> crt_and_rename_vars inner (MAP.add name (HM_Elem (gen())) map)
	| _ -> rename tp map SET.empty;;
	
(* Apply substitution to type *)
let apply_subst_to_type tp subst = rename tp subst SET.empty;;
	
(* Apply substitution to another context *)
(* map -> map -> map *)
let apply_subst_to_context s1 context = 
	MAP.map (fun tp -> apply_subst_to_type tp s1) context;;

let print_substs s = MAP.iter (fun k v -> print_string(k^" to "^(hmt_to_string v)^"\n"	)) s;;
	
(* Substitutions composition *)
let subst_comp s1 s2 = 
(*print_string "printing subst_comp\n";*)
	(*print_substs s1;*)
	(*print_substs s2;*)
	let temp = MAP.map (fun tp -> apply_subst_to_type tp s1) s2 in 
	let res = MAP.fold (fun k v mp -> if MAP.mem k mp then mp else MAP.add k v mp) s1 temp in
	(*print_substs res; *)
	res;;
	
let rec free_vars_lmb_helper l blocked = match l with
	HM_Var var -> if (SET.mem var blocked) = true then SET.empty else SET.singleton var
	| HM_Abs (var, lmb) -> free_vars_lmb_helper lmb (SET.add var blocked)
	| HM_App (lhs, rhs) -> SET.union (free_vars_lmb_helper lhs blocked) (free_vars_lmb_helper rhs blocked)
	| HM_Let (var, e1, e2) -> SET.union (free_vars_lmb_helper e1 blocked) (free_vars_lmb_helper e2 (SET.add var blocked));;
(* Get free vars of hm_lambda *)
let rec free_vars_lmb lmb = free_vars_lmb_helper lmb SET.empty;;


let rec free_vars_tp_helper tp blocked = match tp with 
	HM_Elem var -> if SET.mem var blocked then SET.empty else SET.singleton var 
	| HM_Arrow (lhs, rhs) -> SET.union (free_vars_tp_helper lhs blocked) (free_vars_tp_helper rhs blocked)
	| HM_ForAll (var, t) -> free_vars_tp_helper t (SET.add var blocked);;
(* Get free vars of hm_type *)
let rec free_vars_tp tp = free_vars_tp_helper tp SET.empty;;

(* Get free vars of context *)
let rec free_vars_context context = 
		MAP.fold (fun var tp st -> SET.union st (free_vars_tp tp)) context SET.empty;;

(* Zamykanie contexta *)		
let rec zamyk context tp = let fvtp = free_vars_tp tp in		
							let fv_cont = free_vars_context context in	
							SET.fold (fun tp res -> if SET.mem tp fv_cont then res else HM_ForAll (tp, res)) fvtp tp;;

(* Converts hm_type to algebraic_term *)
let rec hm_to_alg tp = match tp with
	HM_Elem var -> Hw2_unify.Var var 
	| HM_Arrow (lhs, rhs) -> Hw2_unify.Fun ("arrow", [hm_to_alg lhs; hm_to_alg rhs])
	| HM_ForAll (var, t) -> Hw2_unify.Fun ("forall", [Hw2_unify.Var var; hm_to_alg t]);;

(* Converts algebraic_term to hm_type *)
let rec alg_to_hm alg = match alg with 
	Hw2_unify.Var var -> HM_Elem var 
	| Hw2_unify.Fun ("arrow", f::s::[]) -> HM_Arrow (alg_to_hm f, alg_to_hm s)
	| Hw2_unify.Fun ("forall", (Hw2_unify.Var var)::s::[]) -> HM_ForAll (var, alg_to_hm s)
	| _ -> failwith "shouldn't be such algebraic term";;

let print_type tp = print_string ((hmt_to_string tp) ^"\n");;
	
let rec print_term term = match term with 
Hw2_unify.Var a -> print_string (a^" ")
| Hw2_unify.Fun(name, ls) -> print_string (name ^ "(");
					List.iter print_term ls; 
					print_string ") ";;

	
let rec algorithm_w_impl lmb context = 
(*	print_string ("impl\t"^(hmv_to_string lmb)^"\n");*)
	match lmb with 
	HM_Var a -> let tp = MAP.find a context in 
						(MAP.empty, crt_and_rename_vars tp MAP.empty)
	| HM_Abs (var, er) -> let e = HM_Elem (gen()) in
							let t = MAP.add var e context in
							let (s, tp) = algorithm_w_impl er t in
						(*	print_type tp;*)
							(s, HM_Arrow (
							apply_subst_to_type (MAP.find var t) s, tp))
	| HM_App (lhs, rhs) -> let (s1, t1) = algorithm_w_impl lhs context in		
							let (s2, t2) = algorithm_w_impl rhs (apply_subst_to_context s1 context) in 
(*							print_string "HM_App\n";
							print_type t1;
							print_type t2;*)
							let nw = HM_Elem (gen()) in 
							(match (Hw2_unify.solve_system 
									[(hm_to_alg (apply_subst_to_type t1 s2), 
									hm_to_alg (HM_Arrow (t2, nw)))]) with 
								None -> raise NoTypeExists
								| Some x -> 
(*									List.iter (fun (name, term) -> print_string (name^"="); print_term term; print_string "\n") x;*)
											let xmap = List.fold_left 
												(fun mp (k, v) -> MAP.add k (alg_to_hm v) mp) MAP.empty x in
											let s = subst_comp xmap (subst_comp s2 s1) in 
											(s, apply_subst_to_type nw s)
							)
									
	| HM_Let (var, e1, e2) -> 
	print_string "here\n";
							let (s1, t1) = algorithm_w_impl e1 context in							
							
							print_string(string_of_hml e1);
							print_type t1;
MAP.iter (fun k v -> print_string (k^":"^(hmt_to_string v)	^"\n")) s1;						
print_string "\n\n";
							let nw_cont = apply_subst_to_context s1 context in 
							let nw_cont_fin = (MAP.add var (zamyk nw_cont t1) nw_cont) in 
							let (s2, t2) = algorithm_w_impl e2 nw_cont_fin in
							(subst_comp s2 s1, t2);;
				

				
let algorithm_w lmb = 
			(*print_string ("test\n"^(hmv_to_string lmb)^"\n");*)
			let fv_lm = free_vars_lmb lmb in
					  let context = SET.fold (fun var mp -> MAP.add var (HM_Elem (gen())) mp) fv_lm MAP.empty in
					  MAP.iter (fun k v -> print_string (k^":"^(hmt_to_string v)	^"\n")) context;
						try let (s, tp) = algorithm_w_impl lmb context in 
							Some (MAP.bindings s, apply_subst_to_type tp s)
						with _ -> None;;

let a = HM_Var "a";;
let x = HM_Var "x";;
let y = HM_Var "y";;
let z = HM_Var "z";;

let b = HM_Abs("y", HM_Abs("z", HM_App (x, HM_App(y, z))));;
let c = HM_App (x, z);;
(*\x.x*)
let d = HM_Abs("x", x);;
(*\x.\y.x*)
let e = HM_Abs("x", HM_Abs("y", x));;

(*\x.\y.\z.xz(yz)*)
let f = HM_Abs("x", HM_Abs("y", HM_Abs("z", HM_App(HM_App(x, z), HM_App(y, z)))));;

let id = HM_Var "id";;
(* let id = \\x.x in \\f.\\x.id (id (id x)) *)
let t1t = HM_Let ("id", HM_Abs("x", x), HM_Abs("f", HM_Abs("x", HM_App(id, HM_App(id, HM_App(id, x))))));;

let t2t = "let id = \\x.x in \\f.\\x.id f (id (id x))";; 
let t3f = "let id = \\x.x in \\f.\\x.id f (id x (id x))";; 
(* let id = \\t.t in \\f.\\x.(id f) (id x) *)
let t = HM_Var "t";;
let f = HM_Var "f";;
let t4t = HM_Let ("id", HM_Abs("t", t), HM_Abs("f", HM_Abs("x", HM_App(HM_App(id, f), HM_App(id, x)))));;

let t5t = HM_Abs("f", HM_Abs("x", HM_App(f, HM_App(f, x))));;

let t6t = "let id = \\t.t in (id f) (id x)";; 

let a = HM_Var "a";; let b = HM_Var "b";;
let pow = HM_Abs("a", HM_Abs("b", HM_App (b, a)));;


let t = hml_of_string("let x = \\f.\\c.f (f c) in x x x x x x")	;;
let t6t = hml_of_string("let dd = \\f.\\c.f (f c) in dd dd dd dd dd dd");; 

let test = t6t in
print_string ("test\n"^(hmv_to_string test)^"\n");
match algorithm_w test with 
	None -> print_string "NONE\n\n"
	| Some (ls, tp) -> 
		print_string "Ok\n";
		List.iter (fun (var, tp) -> print_string (var^":"^(hmt_to_string tp)^"\n")) ls;
		print_string ("type" ^ (hmt_to_string tp));;