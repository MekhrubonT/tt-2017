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
	

let rec term_to_string term = match term with 
	Var a -> a
	| Fun(name, ls) -> name ^ "(" ^ (data_to_string ls)^ ")"
and data_to_string data = match data with
	[] -> ""
	| last::[] -> term_to_string last
	| hd::tail -> (term_to_string hd) ^ "," ^ (data_to_string tail);;
let print_term term = print_string (term_to_string term);;
let print_term_e term = print_term term; print_newline();;

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
		else (
			print_endline ("got different fucntions "^ln^rn);
			raise NoSolution
		)
	| (Fun (n, l), Var v)::tail -> solve ((Var v, Fun (n, l))::tail) prefix 
	| (Var var, r)::tail -> 
		if equals (Var var) r then (
			solve tail prefix 
		) else if contains_var var r then (
			print_endline ("got "^var^" in "^(term_to_string r));
			raise NoSolution
		) else (
			solve (List.map (fun(a, b) -> (apply_substitution [var, r] a,
					apply_substitution [var, r] b)) tail)
				((var, r)::prefix)
		);;

let solve_system equations = try Some (solve equations []) with _ -> None;;

let checker system = 
	List.iter (fun (lhs, rhs) -> print_term(lhs); print_string ("="); print_term rhs; print_string "\n") system;
	print_string "\n";

	match solve_system system with 
	None -> print_string "none\n";
	| Some ls -> 
		List.iter (fun (name, term) -> print_string (name^"="); print_term term; print_string "\n") ls;
		print_string "----------\n";
		if check_solution ls system = false then 
			print_endline "fail"
		else 
			print_endline "correct solution";
	;;


(*		

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
*)
let substr str lb rb = String.trim (String.sub str lb ((String.length str) - rb - lb));;

exception ParseException;;

let parse_term str = 	
	
	let rec find_next_div pos = 
		if pos = String.length str || 
				str.[pos] = '(' || str.[pos] = ',' || str.[pos] == ')' then (
			pos 
		) else (
			find_next_div (pos + 1);
		) in	
	let rec parse_head start = 
		let pos = find_next_div start in
		let head = String.sub str start (pos - start) in
		if pos = String.length str || str.[pos] <> '(' then (
			(Var head, pos)
		) else (
			let (data, fin) = parse_args (pos + 1) in
			(Fun (head, data), fin)
		) 
	and parse_args start = 
		let (cur, pos) = parse_head start in 
		if str.[pos] = ',' then (
			let (tail, fin) = parse_args (pos + 1) in
			(cur::tail, fin)
		) else (
			([cur], pos + 1)
		)
	in
	let (term, len) = parse_head 0 in 
	if len <> String.length str then 
		raise ParseException 
	else 
		term
	;;

let t1 = ("h95(f1(h57(d42(g30(j88,s83,p38,q73,y71),d63(v26,q58)),a87(e23(t57),f59(q31),d48(v32))),e80(a21(a80(x21,p5,u94,v9),h30(t72,q93,l60,w85,n38),e21(z96,w18,k39,l28)),m64,h8(h40(y65,v27,v95,j43),c30(n89)))),a18(k14,f49(x37),f82(e79(a17(p2),i69,g20(w51,x64,o61,p13,q95),h50(i81,k68,k73,z22,u37)),c9(i6,a65(j91,i93,t9,t18),g16(z85,y14,v88,s7)),f30(f88(v18,j6,n24,z18,p1),g50(j83),c16(p77,r68,j40),x82,f19(o14,p66,t24,q82)),c14(d48(p99),c57(u98),c14(s60,i71,v32),h55(k44,k69),b89(p63,k26,j71,t89,k11))),g49(c47(c42(r23,j9),h76(l38,n57,y54,w73),c89(y18,m45,r71,o6,o67),f92(t54,y5)),s0,a30(a39(u13,w15),h18(i0)),g76(x83)),k77),c58(a69(b63(g50(v33,i58,v51,w71),d73(s10)),d20(c41(r55,n10,o26,r17,i82),e10(s70,j22,z45,k40,l58),d71(v58,s38,l36,q20),a78(u88,w78,o11)),c54(d98(i1,r16,v3),e49(x54,u10)),f66(c20(q24,m95,l42),g0(s82,o9,j71,z51,n26),f46(r50,l82),g17(u29,w38,l81))),b23(a0(e66(o37,u96,u35,o95),d81(u7,w44,l51,s25,x3),b14(o26,v71),h5(p56,w1),b27(i34)),e47(y90,b72(t48,s75,n16,n49,q84),f86(p69,o24,j76,y42),o91),a84(f47(o84,y22,s69,y79,x19)),d34(a86(r52,l15),d29(t12,x68,s64,i86),h11(l17,l13,z8,n39,o42),h47(p77,x33,j21,m41,u76))),b69(d96(e66(l47,x20,s92,t4,z67),e9(o3,i86,x70),f26(j55,k24,v31,t75,x40),d66(u20,k29,q71,i53,n40))),c99(a0(b90(r18,p64,w25,y74,q83),g19(o48,q71,j43,i23,m85)),d87(d84(l12,q41,l82,o26,r42)),b84(h26(r99),f3(y11,l67)),l26)),e54(a93(r41,c48(g40(v84,r44)),b69(e61(k49,p5,i83,x91,j63)),g62(w58,b90(v28,i50,l88),x56,e10(x9,o20,q24,u36)),d5(a85(x46,j92,q34,p21,t82),b4(z33,z40,o13,y15))),b51(f26(g77(v20,j58),c60(m57,r54,s11,i72,u50),e39(o27),g32(r52,m67,r48,s87,k53),e27(u72,j3)),d66(b34(p9),a33(o21,i48,z16),o18),g22(h72(n94,m69,r58,k53,w70)),e73(h91(u40,y78,w51,p19,x20),f87(m48,k26,n44,v18),c9(o55,j79,r33,r39,k49))),g90(f51(c65(u21,q76,p62,s90,z11),c70(r46),h70(y48,x69)),f92(e87(t84,k46,p61,u14,n82)),e98(p51,b30(r4,j37),s14,e41(x53,o27,y92,p13,v89)),b94(e37(t39,n24,q56,t12,k45),g4(z81),b41(v25,q66,o80),h65(w70,w70,w60),b84(x39)))))");;
let t2 = ("h95(f1(h57(d42(g30(j88,s83,p38,q73,y71),d63(v26,t59)),a87(e23(t57),f59(q31),d48(v32))),v0),a18(h51(a26(e31(n58,z82,i19,o88),c88(p85,q31),h71(k27,r23,i76,s28),b7(s55)),a75(a80(m20,n21,k64,u7,w25),g36(q84)),g23(h92(n54,t67,p3,p20),a69(k21,w68,m78,j60)),d37(a13(i65),b44(q44,j40,n72,z76,o60),f51(m44,v16,m61))),f49(e50(a92(s16,o42,o36,i73))),f82(e79(a17(p2),f99(m82),g20(w51,x64,o61,p13,q95),h50(i81,k68,k73,x99,u37)),c9(g6(p29),a65(j91,i93,t9,t18),g16(z85,y14,v88,s7)),f30(f88(v18,z57,j37,z18,p1),g50(t77),c16(o86,r68,j40),h60(o16,s14,t84,j87),f19(o14,p66,t24,q82)),c14(d48(p99),c57(q0),c14(s60,i71,v32),h55(k44,k69),b89(k68,k26,i75,t89,w20))),g49(c47(c42(r23,s57),h76(l38,t10,y54,w73),c89(y18,m45,r71,o6,o67),p85),u72,a30(a39(p32,u23),h18(i0)),g76(s87)),b67(c45(a10(j62,o61,z41),e55(l7,w24,w76),e83(k64)),h10(g54(y92,w25,r47,j47,z51),e56(m44),d9(k82,i47,u87,i44),h44(s52,s6,p98)),c22(g71(l18,n76,w21)),n92,p24)),c58(a69(b63(g50(v33,i58,v51,w71),d73(s10)),d20(c41(r55,n10,o26,r17,i0),e10(s70,j22,z45,k40,l58),d71(v58,s38,t87,q20),q94),c54(d98(i1,r16,v3),e49(x54,u10)),f66(c20(q24,m95,l42),g0(s82,o9,j71,z51,n26),f46(i43,l82),g17(u29,w38,l81))),b23(l83,e47(e80(x60,o91,z82),b72(t48,s75,n16,n49,q84),f86(p69,o24,j76,y42),g56(s81,p25)),a84(r14),d34(a86(r52,r92),d29(t12,s79,s64,i86),h11(l17,l13,z8,n39,o42),h47(p77,x33,j21,m41,u76))),b69(d96(e66(l47,x20,s92,n24,z67),e9(o3,i86,x70),f26(j55,q44,v31,t75,x40),i13)),c99(a0(b90(r18,p64,w25,y74,r53),g19(o48,n71,j43,i23,m85)),d87(d84(l12,q41,l82,o26,r42)),b84(h26(z78),f3(y11,l67)),h57(b97(q12,y82,m18,x67)))),e54(a93(a20(h42(i78,z34,u76,k60),e54(y47,v57),a77(i2,r90,k5,o58),d46(v55,q52,o39),d83(t99,v96,l2,n18)),c48(g40(v84,r44)),b69(e61(k49,p5,i83,x91,l32)),g62(g40(y9,u92,m12,p77,v30),b90(v28,i50,l88),h50(z28,i38,v88,j95,y91),e10(t75,n14,p72,m24)),w11),b51(f26(g77(v20,j58),c60(m57,r54,s11,i46,u50),e39(o27),g32(r52,m67,r48,s87,k53),e27(u72,j3)),d66(b34(p9),r73,d31(u41,t58,l13)),g22(h72(n94,m69,r58,k53,w70)),e73(h91(u40,y78,w51,p19,z80),f87(m48,k26,n44,v18),c9(o55,j79,r33,r39,j44))),g90(f51(c65(s14,q76,p62,s90,u21),c70(o11),h70(y48,x69)),f92(e87(t84,n20,p61,u14,n82)),e98(b15(z80,x51,m76,r34,k80),b30(q37,v79),a14(r52,k96,v68,v89),e41(x53,o27,y92,p13,v89)),b94(r74,g4(z81),b41(v25,q66,o80),h65(w70,w70,w60),b84(r62)))))");;

let l1 = parse_term "h95(f1(h57(d42(g30(j88,s83,p38,q73,y71),d63(v26,q58)),a87(e23(t57),f59(q31),d48(v32))),e80(a21(a80(x21,p5,u94,v9),h30(t72,q93,l60,w85,n38),e21(z96,w18,k39,l28)),m64,h8(h40(y65,v27,v95,j43),c30(n89)))),a18(k14,f49(x37),f82(e79(a17(p2),i69,g20(w51,x64,o61,p13,q95),h50(i81,k68,k73,z22,u37)),c9(i6,a65(j91,i93,t9,t18),g16(z85,y14,v88,s7)),f30(f88(v18,j6,n24,z18,p1),g50(j83),c16(p77,r68,j40),x82,f19(o14,p66,t24,q82)),c14(d48(p99),c57(u98),c14(s60,i71,v32),h55(k44,k69),b89(p63,k26,j71,t89,k11))),g49(c47(c42(r23,j9),h76(l38,n57,y54,w73),c89(y18,m45,r71,o6,o67),f92(t54,y5)),s0,a30(a39(u13,w15),h18(i0)),g76(x83)),k77),c58(a69(b63(g50(v33,i58,v51,w71),d73(s10)),d20(c41(r55,n10,o26,r17,i82),e10(s70,j22,z45,k40,l58),d71(v58,s38,l36,q20),a78(u88,w78,o11)),c54(d98(i1,r16,v3),e49(x54,u10)),f66(c20(q24,m95,l42),g0(s82,o9,j71,z51,n26),f46(r50,l82),g17(u29,w38,l81))),b23(a0(e66(o37,u96,u35,o95),d81(u7,w44,l51,s25,x3),b14(o26,v71),h5(p56,w1),b27(i34)),e47(y90,b72(t48,s75,n16,n49,q84),f86(p69,o24,j76,y42),o91),a84(f47(o84,y22,s69,y79,x19)),d34(a86(r52,l15),d29(t12,x68,s64,i86),h11(l17,l13,z8,n39,o42),h47(p77,x33,j21,m41,u76))),b69(d96(e66(l47,x20,s92,t4,z67),e9(o3,i86,x70),f26(j55,k24,v31,t75,x40),d66(u20,k29,q71,i53,n40))),c99(a0(b90(r18,p64,w25,y74,q83),g19(o48,q71,j43,i23,m85)),d87(d84(l12,q41,l82,o26,r42)),b84(h26(r99),f3(y11,l67)),l26)))";;                                              
let l2 = parse_term "h95(f1(h57(d42(g30(j88,s83,p38,q73,y71),d63(v26,t59)),a87(e23(t57),f59(q31),d48(v32))),v0),a18(h51(a26(e31(n58,z82,i19,o88),c88(p85,q31),h71(k27,r23,i76,s28),b7(s55)),a75(a80(m20,n21,k64,u7,w25),g36(q84)),g23(h92(n54,t67,p3,p20),a69(k21,w68,m78,j60)),d37(a13(i65),b44(q44,j40,n72,z76,o60),f51(m44,v16,m61))),f49(e50(a92(s16,o42,o36,i73))),f82(e79(a17(p2),f99(m82),g20(w51,x64,o61,p13,q95),h50(i81,k68,k73,x99,u37)),c9(g6(p29),a65(j91,i93,t9,t18),g16(z85,y14,v88,s7)),f30(f88(v18,z57,j37,z18,p1),g50(t77),c16(o86,r68,j40),h60(o16,s14,t84,j87),f19(o14,p66,t24,q82)),c14(d48(p99),c57(q0),c14(s60,i71,v32),h55(k44,k69),b89(k68,k26,i75,t89,w20))),g49(c47(c42(r23,s57),h76(l38,t10,y54,w73),c89(y18,m45,r71,o6,o67),p85),u72,a30(a39(p32,u23),h18(i0)),g76(s87)),b67(c45(a10(j62,o61,z41),e55(l7,w24,w76),e83(k64)),h10(g54(y92,w25,r47,j47,z51),e56(m44),d9(k82,i47,u87,i44),h44(s52,s6,p98)),c22(g71(l18,n76,w21)),n92,p24)),c58(a69(b63(g50(v33,i58,v51,w71),d73(s10)),d20(c41(r55,n10,o26,r17,i0),e10(s70,j22,z45,k40,l58),d71(v58,s38,t87,q20),q94),c54(d98(i1,r16,v3),e49(x54,u10)),f66(c20(q24,m95,l42),g0(s82,o9,j71,z51,n26),f46(i43,l82),g17(u29,w38,l81))),b23(l83,e47(e80(x60,o91,z82),b72(t48,s75,n16,n49,q84),f86(p69,o24,j76,y42),g56(s81,p25)),a84(r14),d34(a86(r52,r92),d29(t12,s79,s64,i86),h11(l17,l13,z8,n39,o42),h47(p77,x33,j21,m41,u76))),b69(d96(e66(l47,x20,s92,n24,z67),e9(o3,i86,x70),f26(j55,q44,v31,t75,x40),i13)),c99(a0(b90(r18,p64,w25,y74,r53),g19(o48,n71,j43,i23,m85)),d87(d84(l12,q41,l82,o26,r42)),b84(h26(z78),f3(y11,l67)),h57(b97(q12,y82,m18,x67)))))";;                                     

let no_solution = [(parse_term "f(x)", parse_term "y"); (parse_term "f(x)", parse_term "f(y)")];;
let solveable1 = [(parse_term "f1(k,f2(l,f3(m,f4(n,f5(o)))))", parse_term "f1(f2(f3(f4(f5(o),n),m),l),k)")];;
let solveable2 = [(parse_term "f(x,g(y))", parse_term "f(e(g(f(t,z))),t)")];;
let solveable3 = [(parse_term "e20(h79(f80(h99(a77(z25,m70,k82,q28,u48),g83(w4),b23(s74,y50,j58),h72(m89,k67,y98),a24(m37)),c29(h20(t62,w19,j28,r11),b99(w36,k41,q66),d76(o89,k50),h48(i31,s24,s94,s26),b13(l83,o3,k18,u23)),e97(f92(i17,k98,v60,k89,l54)),h50(a30(r45,p38,y50,i36),a42(o96,q4,p26,v7,s15),w71,b91(x87),d92(k0,u11,w68)),y93),g14(g66(v5))),d35(a25(b85(e43(o98,l75,j79,z73),g20(z5,w27,p80,m66)),b71(d38(m7,t5,i12,o65),f39(s36,w76,w48),e10(n36,u42,q50,r90,y68),d53(q93,r65,r37),t15),d53(c36(s42,u9),f31(u84,p34,m94,l88,y54),f64(i51,j10,i27)),g47(e70(o96,l61,o1,v23))),a93(d38(g76(t14,s21,n5,w73,o74),c72(k90,n14,j91,j44,j17)),h58(d81(q49,t90,t13,m76,r47),f40(q94,y0,t83)),h10(c66(w26),g27(k96,w93),c16(j77,q54,w97,t54,o21),g31(z22,t97),f71(l30,m59,z77,x44))),e9(h38(a80(m11,z59,v15),f19(l21,j13,x42)),e79(g72(t7,m44,z83),b73(u54,m4,r18,q98,p39),g89(q35,y84)),h60(x9)),a92(f71(g8(n58,y37,z24,x53),b67(t51,v96,l91,s97),f73(p39,z76,l15,z33,y49)),f32(c94(y51)))),z16,d72(h88(a81(h97(z95,m96,p42,w27),a80(l77,l51,x26),a74(q44,k61,p1)),g38(c49(i96,m36,t45))),c48(b24(e91(y57,k7,w3),q98,c56(z61,y89,u67)),e36(a50(o28,p88,i48,u72,w71),e55(o60)),g75(g38(u85),e86(i41,n43,s6,r84),d25(m33),s76),b97(f99(u35,t76,l43,y73)),g98(f75(v0,k3),b11(u58,m34)))),e88(g38(l74,c14(q82,f1(x61,q13),e18(y55,x16,r29)),e60(f82(x10,v0,k98,v40,p91),h97(j54,o45,v76,r81),a74(z28,k60,j48,q88),b42(t56,o16,n98),e83(y10)),e25(c13(k11,u87,x15,y44),g65(j69,l66,i89,w42,o17),b43(t77,w29,n97,u25,r61),g52(v35)),e9(c2(z61,t39,u93,y43),g65(z58,i96),a76(v77,r28,p95,n86,m95),h43(n88,m94,j5,s57))),f33(h88(c45(l2,s18,j88)),c31(n94,h60(j52,u9),h28(n65,j77,r54,t59),h85(m44),e66(t73,o68,n17))),j25,e18(d10(h99(p86,i52,v95),c44(p71,t97,k24),e80(n97,n93,z46))),f82(c38(g62(j10,n72,v84,y80),f43(z96,o84,q8,s1,o77),a10(n81,z95)),g41(f5(w95,u47,k90),g12(u45),a81(j5)),e68(f67(p15,j60,q50,x95,i63),a13(u9)),e36(m68,b71(z54,z73)))))", parse_term "e20(h79(f80(h99(a77(z25,m70,k82,q28,x57),g83(w4),b23(s74,y50,p12),u4,a24(m37)),c29(h20(k77,w19,w29,n1),b99(w36,k41,q66),d76(o89,k50),h48(i31,s24,p6,s26),b13(l83,o3,k18,u23)),e97(f92(v41,k98,x5,k89,l54)),h50(a30(r14,p38,y50,i36),a42(o96,q4,p26,v7,s15),g29(v88,z0,t93,r37),b91(x87),d92(k0,u11,j87)),d85(t91)),g14(g66(b31(y64,n76,r11,n5,r10)))),z32,e87(b72(c70(h99(n43),h73(k53,r71,v90),a12(i30,p89,p4),g78(k20),h36(q91,y66,q76,m49)),g20(b24(r90,k3,s56,x43),a19(k56,q44))),e25(g61(f40(t27,l9,o49,w16,y87),g91(r52,u65,t36,z15)))),d72(h88(a81(h97(z95,m96,p42,w27),a80(l77,l51,x26),a74(q44,s95,p1)),g38(c49(i96,m36,t45))),c48(b24(e91(y57,k7,w3),e91(w42),c56(z61,j36,i38)),e36(a50(o28,p88,i48,u72,w71),e55(o60)),g75(g38(u85),e86(i41,n43,s6,m91),d25(m33),g94(k99,l98)),b97(f99(u35,t76,l43,y73)),g98(f75(v0,k3),m57))),e88(g38(e71(e39(w53,i31,q73),f42(s33,z81)),c14(c16(v16,v57),f1(l83,q13),e18(y55,x16,r29)),e60(f82(x10,v0,k98,v40,p91),v59,a74(u75,k60,j48,q88),b42(t56,o16,n98),e83(y10)),m12,e9(c2(z61,t39,u93,y43),g65(z58,i96),a76(v77,r28,m23,n86,m95),h43(n88,m94,j5,s57))),f33(h88(c45(j46,s18,j88)),c31(b50(o21),h60(j52,u9),h28(y36,s21,r54,t59),h85(k52),e66(t73,o68,t88))),b69(z30,d93(c70(s78,y41,q53),d16(l56),h81(u61,o65,s15),g44(s53,v88,r93,j27)),c62(b91(w50,q92),d41(j52,z16,o67))),e18(d10(h99(p86,i52,v95),c44(p71,j4,k24),e80(n97,n93,j58))),f82(c38(g62(j10,n72,z6,y80),f43(k23,o84,q8,s1,o77),a10(n81,z95)),g41(f5(w95,u47,k90),g12(o66),a81(j5)),i60,e36(f72(k46),b71(z54,z73)))))")];;
(*
checker no_solution;;
*)
