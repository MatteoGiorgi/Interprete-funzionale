(* ambiente *)
module type ENV =
	sig
		type 't env
		val emptyenv : 't -> 't env
		val applyenv : 't env * string -> 't
		val bind : 't env * string * 't -> 't env
		exception WrongBindlist
		val bindlist : 't env * (string list) * ('t list) -> 't env
end

module Funenv =
	struct
		type 't env = string -> 't
		let emptyenv (x) = function (y: string) -> x
		let applyenv (x,y) = x y
		let bind (r,l,e) = function lu -> if lu = l then e
										  else applyenv(r,lu)
		exception WrongBindlist
		let rec bindlist(r,il,el) =
			match (il,el) with
			| ([],[]) -> r 
			| (i::ill,e::ell) -> bindlist(bind(r,i,e),ill,ell)
			| _ -> raise WrongBindlist
end;;

module Listenv:ENV =
	struct
		type 't env = (string * 't) list
		let emptyenv(x) = [("", x)]
		let rec applyenv(x, y) = match x with
			| [(_, e)] -> e
			| (i1, e1) :: x1 -> if y = i1 then e1
								else applyenv(x1, y)
			| [] -> failwith("wrong env")
		let bind(r, l, e) = (l, e)::r
		exception WrongBindlist
		let rec bindlist(r, il, el) =
			match (il, el) with
			| ([], []) -> r
			| (i::il1, e::el1) -> bindlist (bind(r, i, e), il1, el1)
			| _ -> raise WrongBindlist
end

open Funenv;;

(* interprete *)
type exp =
	| Eint of int
	| Ebool of bool
	| Den of ide
	| Prod of exp * exp
	| Sum of exp * exp
	| Diff of exp * exp
	| Eq of exp * exp
	| Minus of exp
	| Iszero of exp
	| Or of exp * exp
	| And of exp * exp
	| Not of exp
	| Ifthenelse of exp * exp * exp
	| Let of ide * exp * exp
	| UFun of ide * exp
	| UAppl of exp * exp
	| Fun of ide list * exp
	| Appl of exp * exp list
	| Rec of ide * exp
	| Etup of tuple
	| Pipe of tuple
	| ManyTimes of int * exp
and ide = string
and tuple =
	| Nil
	| Seq of exp * tuple
;;

type eval =
	| Int of int
	| Bool of bool
	| Unbound
	| Funval of efun
	| TupVal of eval list
and efun = exp * eval env
;;


let typecheck (x,y) =
	match x,y with
	| "int",Int(_) -> true
	| "bool",Bool(_) -> true
	| "fun",Funval(_) -> true
	| "tup",TupVal(_) -> true
	| a,_ when a="int" || a="bool" || a="fun" || a="tup" -> false
	| _ -> failwith ("not a valid type")
;;

let minus x =
	if typecheck("int",x) then(
		match x with 
		| Int(y) -> Int(-y)
		| _ -> failwith("impossible"))
	else failwith("type error")
;;

let iszero x =
	if typecheck("int",x) then(
		match x with 
		| Int(y) -> Bool(y=0)
		| _ -> failwith("impossible"))
	else failwith("type error")
;;

let equ (x,y) =
	if typecheck("int",x) && typecheck("int",y) then(
		match (x,y) with 
		| (Int(u),Int(w)) -> Bool(u=w)
		| _ -> failwith("impossible"))
	else failwith("type error")
;;

let plus (x,y) =
	if typecheck("int",x) && typecheck("int",y) then(
		match (x,y) with 
		| (Int(u),Int(w)) -> Int(u+w)
		| _ -> failwith("impossible"))
	else failwith("type error")
;;

let diff (x,y) =
	if typecheck("int",x) && typecheck("int",y) then(
		match (x,y) with 
		| (Int(u),Int(w)) -> Int(u-w)
		| _ -> failwith("impossible"))
	else failwith("type error")
;;

let mult (x,y) =
	if typecheck("int",x) && typecheck("int",y) then(
		match (x,y) with 
		| (Int(u),Int(w)) -> Int(u*w)
		| _ -> failwith("impossible"))
	else failwith("type error")
;;

let non (x) =
	if typecheck("bool",x) then(
		match (x) with
		| Bool(true) -> Bool(false)
		| Bool(false) -> Bool(true)
		| _ -> failwith("impossible"))
	else failwith("type error")
;;

let vel (x,y) =
	if typecheck("bool",x) then(
		match (x) with
		| Bool(true) -> x
		| _ ->	if typecheck("bool",y) then y
				else failwith("type error"))
	else failwith("type error")
;;

let et (x,y) =
	if typecheck("bool",x) then(
		match (x) with
		| Bool(false) -> x
		| _ ->	if typecheck("bool",y) then y
				else failwith("type error"))
	else failwith("type error")
;;


let rec substitute ((b:exp),(x:ide),(check:bool)) =
	let rec subtup =
			(function
			| Nil -> Nil
			| Seq(e,rest) -> Seq(substitute(b,x,check) e, subtup rest))
	in
	(function
	| Den(y) when y=x -> b
	| Den(y) when y="__x" && check -> failwith ("__x not allowed as ide")
	| Prod(e1,e2) -> Prod(substitute(b,x,check) e1, substitute(b,x,check) e2)
	| Sum(e1,e2) -> Sum(substitute(b,x,check) e1, substitute(b,x,check) e2)
	| Diff(e1,e2) -> Diff(substitute(b,x,check) e1, substitute(b,x,check) e2)
	| Eq(e1,e2) -> Eq(substitute(b,x,check) e1, substitute(b,x,check) e2)
	| Minus(e) -> Minus(substitute(b,x,check) e)
	| Iszero(e) -> Iszero(substitute(b,x,check) e)
	| Or(e1,e2) -> Or(substitute(b,x,check) e1, substitute(b,x,check) e2)
	| And(e1,e2) -> And(substitute(b,x,check) e1, substitute(b,x,check) e2)
	| Not(e) -> Not(substitute(b,x,check) e)
	| Ifthenelse(g,e1,e2) -> Ifthenelse(substitute(b,x,check) g,
										substitute(b,x,check) e1,
										substitute(b,x,check) e2)
	| Let(i,e1,e2) -> if i!=x then Let(i, substitute(b,x,check) e1, substitute(b,x,check) e2)
					  else Let(i, substitute(b,x,check) e1, e2)
	| UFun(i,e) when i!=x -> UFun(i, substitute(b,x,check) e)
	| UAppl(f,arg) -> UAppl(substitute(b,x,check) f, substitute(b,x,check) arg)
	| Fun(il,e) when (List.mem x il)=false -> Fun(il, substitute(b,x,check) e)
	| Appl(f, args) -> Appl(substitute(b,x,check) f, List.map (substitute(b,x,check)) args)
	| Rec(i,e) when i!=x -> Rec(i, substitute(b,x,check) e)
	| Etup(t) -> Etup(subtup t)
	| Pipe(t) -> Pipe(subtup t)
	| ManyTimes(n,e) -> ManyTimes(n, substitute(b,x,check) e)
	| ex -> ex)
;;


let rec sem ((e:exp),(r:eval env)) =
	match e with
	| Eint(n) -> Int(n)
	| Ebool(b) -> Bool(b)
	| Den(i) -> applyenv(r,i)
	| Iszero(a) -> iszero(sem(a,r))
	| Eq(a,b) -> equ(sem(a,r),sem(b,r))
	| Prod(a,b) -> mult(sem(a,r),sem(b,r))
	| Sum(a,b) -> plus(sem(a,r),sem(b,r))
	| Diff(a,b) -> diff(sem(a,r),sem(b,r))
	| Minus(a) -> minus(sem(a,r))
	| And(a,b) -> et(sem(a,r),sem(b,r))
	| Or(a,b) -> vel(sem(a,r),sem(b,r))
	| Not(a) -> non(sem(a,r))
	| Ifthenelse(a,b,c) ->
		let g = sem(a,r)
		in (match typecheck("bool",g) with
			| true -> if g=Bool(true) then sem(b,r)
					  else sem(c,r)
			| _ -> failwith("nonboolean guard"))
	| Let(i,e1,e2) -> sem(e2,bind(r,i,sem(e1,r)))
	| UFun(i,body) -> makeUfun(UFun(i,body),r)
	| UAppl(foo,arg) -> applyUfun(sem(foo,r), sem(arg,r))
	| Fun(i,a) -> makefun(Fun(i,a),r)
	| Appl(e1,e2) -> applyfun(sem(e1,r),semlist(e2,r))
	| Rec(i,e) -> makefunrec(i,e,r)
	| Etup(t) ->
		let rec semtup (tup:tuple) =
			match tup with
			| Nil -> []
			| Seq(e, tt) -> sem(e,r)::semtup(tt)
		in TupVal(semtup(t))
	| Pipe(t) ->
		let rec aux param newBody =
			let reCall i2 body2 tt =
				if param=i2 then
					aux param (substitute(newBody,i2,false) body2) tt
				else
					let newBody2 = substitute(Den "__x",param,true) body2 in
					aux param (substitute(newBody,i2,false) newBody2) tt
			in
			(function
			| Nil -> Funval(UFun(param,newBody),bind(r,"__x",sem(Den(param),r)))
			| Seq(UFun(i2,body2), tt) -> reCall i2 body2 tt
			| Seq(Pipe(t), tt) ->
				(match sem(Pipe(t),r) with
				| Funval(UFun(i2,body2),_) -> reCall i2 body2 tt
				| _ -> failwith("non-functional pipe"))
			| Seq(ManyTimes(m,k), tt) ->
				(match sem(ManyTimes(m,k),r) with
				| Funval(UFun(i2,body2),_) -> reCall i2 body2 tt
				| _ -> failwith("non-functional manytime"))
			| Seq(f,tt) ->
				let clo = sem(f,r) in
				if typecheck("fun",clo) then
					match clo with
					| Funval(UFun(i2,body2),r2) -> reCall i2 body2 tt
					| _ -> failwith("impossible")
				else failwith ("non-functional object"))
		in
		(match t with
		| Nil -> Funval(UFun("x", Den "x"),r)
		| Seq(UFun(i1,body1), tt) -> aux i1 body1 tt
		| Seq(Pipe(t), tt) ->
			(match sem(Pipe(t),r) with
			| Funval(UFun(i1,body1),_) -> aux i1 body1 tt
			| _ -> failwith("non-functional pipe"))
		| Seq(ManyTimes(m,k), tt) ->
			(match sem(ManyTimes(m,k),r) with
			| Funval(UFun(i1,body1),_) -> aux i1 body1 tt
			| _ -> failwith("non-functional manytime"))
		| Seq(f,tt) ->
			let clo = sem(f,r) in
			if typecheck("fun",clo) then
				match clo with
				| Funval(UFun(i1,body1),_) -> aux i1 body1 tt
				| _ -> failwith("impossible")
			else failwith ("non-functional object"))
	| ManyTimes(n,e) ->
		let rec aux cont i body newBody r =
			if cont=1 then
				Funval(UFun(i,newBody),r)
			else
				aux (cont-1) i body (substitute(body,i,false) newBody) r
		in
		(match (n,e) with
		| (n,_) when n<1 -> failwith ("non-positive integer")
		| (_,UFun(i,body)) -> aux n i body body r
		| (_,Pipe(t)) ->
			(match sem(Pipe(t),r) with
			| Funval(UFun(i,body),_) -> aux n i body body r
			| _ -> failwith("non-functional pipe"))
		| (_,ManyTimes(m,k)) ->
			(match sem(ManyTimes(m,k),r) with
			| Funval(UFun(i,body),_) -> aux n i body body r
			| _ -> failwith("non-functional manytime"))
		| (_,f) ->
			let clo = sem(f,r) in
			if typecheck("fun",clo) then
				match clo with
				| Funval(UFun(i,body),r1) -> aux n i body body r1
				| _ -> failwith("impossible")
			else failwith ("non-functional object"))
and semlist ((el:exp list),(r:eval env)) =
	match el with
	| e::ell -> sem(e,r)::semlist(ell,r)
	| [] -> []
and makeUfun (expFun,r) =
	match expFun with
	| UFun(i,a) -> Funval(expFun,r)
	| _ -> failwith ("non-functional object")
and makefun ((a:exp),(r:eval env)) =
	match a with
	| Fun(ii,aa) -> Funval(a,r)
	| _ -> failwith ("non-functional object")
and makefunrec (i,c,r) =
	let functional(rr:eval env) = bind(r,i,Funval(c,rr))
	in let rec(rfix:string->eval) = function x -> (functional rfix) x
	in Funval(c,rfix)
and applyUfun (evalFun,evalArg) =
	if typecheck("fun",evalFun) then
		match evalFun with
		| Funval(UFun(x,a),r1) -> sem(a,bind(r1,x,evalArg))
		| _ -> failwith("impossible")
	else failwith("attempt to apply a non-functional object")
and applyfun ((ev1:eval),(ev2:eval list)) =
	if typecheck("fun",ev1) then
		match ev1 with
		| Funval(Fun(x,a),r1) -> sem(a,bindlist(r1,x,ev2))
		| _ -> failwith("impossible")
	else failwith("attempt to apply a non-functional object")
;;


(*********************************** TEST *************************************)


(*TEST_1*)
sem(
	Let(
		"fact",
		Rec(
			"fact",
			Fun(["x"],
				Ifthenelse(Eq(Den "x",Eint 0),
					Eint 1,
					Prod(Den "x",Appl(Den "fact",[Diff(Den "x",Eint 1)]))
				)
			)
		),
		Appl(Den "fact",[Eint 6])
	),
	emptyenv(Unbound)
)
;;
(*eval = Int 720*)


(*TEST_2*)
sem(
	Etup(
		Seq(Eint(2), Seq(Eint(3), Nil))
	),
	emptyenv(Unbound)
);;
(*eval = TupVal [Int 2; Int 3]*)


(*TEST_3*)
sem(
	Pipe(
		Seq(
			UFun("x",Prod(Eint(2),Den("x"))),
			Seq(UFun("x",Sum(Eint(1),Den("x"))), Nil)
		)
	),
	emptyenv(Unbound)
);;
(*eval = Funval (UFun ("x", Sum (Eint 1, Prod (Eint 2, Den "x"))), <fun>)*)


(*TEST_4*)
sem(
	Let(
		"f",
		Pipe(
			Seq(
				UFun("x",Prod(Eint(2),Den("x"))),
				Seq(UFun("x",Sum(Eint(1),Den("x"))), Nil)
			)
		),
		UAppl(Den("f"),Eint 3)
	),
	emptyenv(Unbound)
);;
(*eval = Int 7*)


(*TEST_5*)
sem(
	Let(
		"x",Eint 33,
		Etup(
			Seq(
				Eint 10,
				Seq(
					Den "x",
					Nil
				)
			)
		)
	),
	emptyenv(Unbound)
)
;;
(*eval = TupVal [Int 10; Int 33]*)


(*TEST_6*)
sem(
	Let(
		"mt",
		ManyTimes(
			10,
			UFun("x", Diff(Den "x", Eint 1))
		),
		UAppl(Den "mt", Eint 100)
	),
	emptyenv(Unbound)
)
;;
(*eval = Int 90*)


(*TEST_7*)
sem(
	Let(
		"p",
		Pipe(
			Seq(
				UFun("x", Diff(Den "x", Eint 3)),
				Seq(
					UFun("y", Sum(Den "y", Eint 3)),
					Nil
				)
			)
		),
		UAppl(Den "p", Eint 10)
	),
	emptyenv(Unbound)
)
;;
(*eval = Int 10*)


(*TEST_8*)
sem(
	Let(
		"p",
		Pipe(
			Seq(
				UFun(
					"x",
					Let(
						"x",Eint 5,
						Diff(Den "x", Eint 3)
					)
				),
				Seq(
					UFun("y", Diff(Den "y", Eint 1)),
					Nil
				)
			)
		),
		UAppl(Den "p", Eint 10)
	),
	emptyenv(Unbound)
)
;;
(*eval = Int 1*)


(*TEST_9*)
sem(
	Let(
		"x", Eint 10,
		Let(
			"p",
			Pipe(
				Seq(
					UFun("x", Sum(Den "x", Eint 1)),
					Seq(
						UFun("y", Sum(Den "y", Den "x")),
						Nil
					)
				)
			),
			UAppl(Den "p", Eint 100)
		)
	),
	emptyenv(Unbound)
)
;;
(*eval = Int 111*)


(*TEST_10*)
sem(
	Let(
		"x", Eint 10,
		Pipe(
			Seq(
				UFun(
					"w",
					Sum(Den "w", Eint 1)
				),
				Seq(
					UFun("y", Sum(Den "w", Den("x"))),
					Nil
				)
			)
		)
	),
	emptyenv(Unbound)
)
;;
(*eval = Funval (UFun ("w", Sum (Den "__x", Den "x")), <fun>)*)


(*TEST_11*)
sem(
	Let(
		"x", UFun("k", Prod(Den "k", Eint 3)),
		Let(
			"p",
			Pipe(
				Seq(
					UFun("x", Sum(Den "x", Eint 1)),
					Seq(
						Den "x",
						Nil
					)
				)
			),
			UAppl(Den "p", Eint 10)
		)
	),
	emptyenv(Unbound)
)
;;
(*eval = Int 33*)


(*TEST_12*)
sem(
	Let(
		"x", UFun("k", Prod(Den "k", Eint 3)),
		Let(
			"p",
			Pipe(
				Seq(
					UFun("x", Sum(Den "x", Eint 1)),
					Seq(
						UFun("y", UAppl(Den "x",Den "y")),
						Nil
					)
				)
			),
			UAppl(Den "p", Eint 10)
		)
	),
	emptyenv(Unbound)
)
;;
(*eval = Int 33*)


(*TEST_13*)
sem(
	Let(
		"k", Eint 3,
		Let(
			"f", UFun("x", Sum(Den "x", Den "k")),
			Let(
				"k", Eint 4,
				UAppl(Den "f", Eint 10)
			)
		)
	),
	emptyenv(Unbound)
)
;;
(*eval = Int 13*)


(*TEST_14*)
sem(
	Let(
		"x", Eint 10,
		Let(
			"p",
			Pipe(
				Seq(
					UFun("x", Sum(Den "x", Eint 1)),
					Seq(
						UFun("__x", Sum(Den "__x", Den "x")),
						Nil
					)
				)
			),
			UAppl(Den "p", Eint 100)
		)
	),
	emptyenv(Unbound)
)
;;
(*Exception: Failure "__x not allowed as ide"*)


(*TEST_15*)
sem(
	Let(
		"__x", Eint 10,
		Let(
			"p",
			Pipe(
				Seq(
					UFun("x", Sum(Den "x", Eint 1)),
					Seq(
						UFun("y", Sum(Den "y", Den "__x")),
						Nil
					)
				)
			),
			UAppl(Den "p", Eint 100)
		)
	),
	emptyenv(Unbound)
)
;;
(*Exception: Failure "__x not allowed as ide"*)
