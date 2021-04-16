open Batteries
open Amodule


type typ =
| Bool
| IntT
| FloatT
| Fun of typ * typ
| Times of typ * typ
| RefT of typ

type pattern = 
| TrueP
| FalseP
| IntP of int
| FloatP of float
| VarP of  typ * string 
| PairP of pattern * pattern 

type memory = 
|Mem of list*(label * expression)

type label =
|Label of int

type expression =
| True
| False
| Int of int
| Float of float
| Var of string
| If of expression * expression * expression
| Lambda of string * typ * expression		(*function*)
| App of expression * expression		(*function application*)
| Match of expression * list * (pattern * expression)

| Pair of expression * expression
| First of expression
| Second of expression
| IsZero of expression
| Plus of expression * expression
| Multiplication of expression * expression
| Ref of expression
| Deref of expression
| Assignment of expression * expression
| Error 


(* SUBSTITUTION FUNCTION FOR APPLICATION-EVALUATOR AND MULTIPLE-SUBTITUTION *)
let rec substitution e v x = 
	match e with 
	| True -> True
	| False -> False
	| Var varname -> if varname = x then v else Var varname
	| Lambda (varname, typ, exp') -> if varname = x then Lambda (varname, typ, exp') else Lambda (varname, typ, substitution exp' v x)
	| App (e1, e2) -> 	App(substitution e1 v x, substitution e2 v x)
	| If(e1, e2, e3) -> If(substitution e1 v x, substitution e2 v x, substitution e3 v x )
	| Pair(e1, e2) -> Pair(substitution e1 v x, substitution e2 v x)		
	| First(e)  -> First(substitution e v x)
	| Second(e) -> Second(substitution e v x)
	| IsZero(e) -> IsZero(substitution e v x)	   	   	   		   	   	   	   	   		
	| Plus(e1, e2) -> Plus(substitution e1 v x, substitution e2 v x)
	| Multiplication(e1, e2) -> Multiplication(substitution e1 v x, substitution e2 v x)

(* GET MAX FUNCTION FOR REFFERENCE EVALUATOR *)
let rec getMax l =
	  | [] -> invalid_arg "empty list"
	  | head::tail -> List.fold_left max head tail 	 
	  
	  
(* LOOK UP FUNCTION FOR DE-REFFERENCE EVALUATOR *)
let rec lookup v l =
match l with
|[] -> 0
| (key,i)::t -> if k = v then i
				else lookup v t;;

(*ADDITION FUNCTION*)	
let add v1 v2 =
	match (v1,v2) with 
   	|(Int n, Int m) -> Int(m+n)
   	|(Int n, Float m) -> Float(float n +. m)
   	|(Float n, Float m) -> Float(n +. m)
    |(Float n, Int m) -> Float(n +. float m)
	|(_, _) -> Error

	
(*MULTIPLICATION FUNCTION*)	
let times v1 v2 =
		match (v1,v2) with 
	   	|(Int(n), Int (m)) -> (Int(m*n))
	   	|(Int(n), Float(m)) -> Float((float_of_int n) *. m)
	   	|(Float(n), Float(m)) -> Float(n *. m)
	    |(Float(n), Int(m)) -> Float(n *. (float_of_int m))
		|(_, _) -> Error


(*MATCH VALUE FUNCTION*)
let rec matchValue v p =
		match (v,p) with
		|(True, TrueP) -> Some []
		|(False, FalseP) -> Some []
		|(value, VarP(typ1,varname)) -> Some [(varname, value)]
		|(Pair(v1,v2), PairP(p1,p2)) -> match matchValue v1 p1 with
										| None -> None
										| Some(bindings1) -> match matchValue v2 p2 with 
															|None -> None
															|Some(bindings2) -> Some (bindings1 @ bindings2)
		| _ -> None


(*MULPTIPLE SUBSTITUTION FUNCTION*)				
let rec multiple_subst body bindings = 
			match bindings with
			|[] -> Error
			|(bindings1) :: restOfBindings -> let bindings1 = (substitution bindings1) in 
													 multiple_subst body restOfBindings 

(*ITERATOR FUNCTION*)
let rec myiterator v clauses = 
	match clauses with
	|[] -> Error
	|((pattern, body)) :: restOfTheList -> match matchValue v pattern with
										   | None -> myiterator v restOfTheList
										   | Some(bindings) -> evaluator (multiple_subst body bindings)	
	
(* EVALUATOR *)
let rec evaluator exp mem = (* return type: (expression, memory) *)
	match exp with
	| True ->  (True, mem)
	| False -> (False, mem)
	| Int e -> (Int e, mem)
	| Float e -> (Float e, mem)
	| Lambda (varname, typ, exp') -> (Lambda (varname, typ, exp'), mem)
	| If(e1, e2, e3) ->  match evaluator e1 with
				 			|Error -> Error
							|True -> (evaluator e2, mem) 
							|False -> (evaluator e3, mem)
	|App (e1, e2) ->  match e1 with 
						| Lambda (varname, typ, exp') -> let v = evaluator e2 in 
														 let mysubs = substitution  exp' v varname in 
														 evaluator (mysubs, mem)			
						| _ -> raise(Failure "App is not complete")					  
	| Pair(e1,e2) -> match evaluator e1 with
		 			|Error -> Error
					| _ -> Pair(evaluator e1, evaluator e2)				
	| First(e)  -> match evaluator e with
		 			|Error -> Error
					| Pair(e1,e2) -> (evaluator e1, mem)
	| Second(e) -> match evaluator e with
					|Error -> Error
					| Pair(e1,e2) -> (evaluator e2, mem)
	| IsZero(e) -> match evaluator e with  
				   |Int(0) -> (True, mem)	
				   |Float(0.0) -> (True, mem)  	   	   	   	   	   	
				   | _ -> (False, mem)   	   	   	   	   	   		   	   	   	   	   		
	| Plus(e1, e2) -> match evaluator e1 with
						|Error -> Error
						| _ -> let v1 = evaluator e1 in 
		 			  			 let v2 = evaluator e2 in
					  		     let myAdd = add v1 v2 in 
					  		   		evaluator (myAdd,mem) 
	| Multiplication(e1, e2) -> match evaluator e1 with
								|Error -> Error
								| _ -> let v1 = evaluator e1 in 
				 			  			 let v2 = evaluator e2 in
							  		     let myTimes = times v1 v2 in 
							  		   		evaluator (myTimes, mem)
	
	| Match(e, clauses) -> match evaluator e1 with
							|Error -> Error
							| _   -> let iter = myiterator (evaluator e, clauses) in
										evaluator (iter, mem)	
	| Ref(e) -> let (v, mem') = evaluator  e mem in
				let mylist = getAllKeys mem' in (* [Label 1, Label 2,...] *)
				let n = getMax mylist in (* 3 *)
				let Label (n+1)  in 
				evaluator (mem' @  [Label (n+1),v])
	| Def(e) -> let (v,mem') = evaluator e mem in 
						evaluator (lookup(v,mem'), mem')
	| Assignment(e1, e2) -> evaluator e1 = Ref(evaluator e2)
 
(* Pretty Printer for TYPE *)																					
let rec prettyPrinter_typ (t : typ ) =
		match t with 
		| Bool -> "Bool"
		| IntT -> "Int"
		| FloatT -> "Float"
		| Fun(t1,t2) -> prettyPrinter_typ t1 ^ " ----> " ^ prettyPrinter_typ t2	
		| Times(t1,t2) -> prettyPrinter_typ t1 ^ " x " ^ prettyPrinter_typ t2	
		
(* Pretty Printer for INTEGER *)		
let rec prettyPrinter_Int (exp: expression) = 
			match exp with
			| Int exp -> print_int exp 
	
(* Pretty Printer for FLOATING POINT *)	
let rec prettyPrinter_Float(exp: expression) = 
				match exp with
				| Float exp -> print_float exp
				
					
(* Pretty Printer for EXPRESSION *)					
let rec prettyPrinter_exp (exp : expression ) = 	
	match exp with 
	| True -> "True"
	| False -> "False"
	| Var(varname) -> varname
	| Lambda (varname, typ, exp') -> "Lambda " ^ varname ^ ": " ^ prettyPrinter_typ typ ^ "." ^ prettyPrinter_exp exp'
	| App (exp1, exp2) -> "(" ^ prettyPrinter_exp exp1 ^ ", " ^ prettyPrinter_exp exp2 ^ ")"
	| If(exp1, exp2, exp3) -> "If " ^ prettyPrinter_exp exp1 ^ " then " ^ prettyPrinter_exp exp2 ^ " else " ^ prettyPrinter_exp exp3
	| Pair(exp1, exp2) -> "Pair: " ^ prettyPrinter_exp exp1 ^ " , " ^ prettyPrinter_exp exp2
	| First(exp) -> "First of " ^ prettyPrinter_exp exp ^ " is: " 

(* Pretty Printer for NEW LINE *)		
let rec prettyPrinter_exp_ln (exp : expression ) = prettyPrinter_exp exp ^ "\n"

(* SUBTYPING FUNCTION *)
let rec subtyping t1 t2 = 
	match (t1,t2) with 
	|(Bool, Bool) -> true
	|(IntT, IntT) -> true
	|(FloatT, FloatT) -> true
	|(IntT, FloatT) -> true
	|(PairT(_, _), PairT(_,_)) -> true
	|(Fun (typ1, typ2), Fun(typ3,typ4)) ->  subtyping typ3 typ1 && subtyping typ2 typ4
	|(RefT(typ1), RefT(typ2)) -> subtyping typ2 typ1
	| _ -> false

(* TYPE CHECKER *)		
let rec type_checker gamma exp = 
	match exp with
	| True -> Bool	
	| False -> Bool
	| App(e1,e2) -> type_checker_App gamma e1 e2
	| If(e1,e2,e3) -> type_checker_If gamma e1 e2 e3
	| IsZero(e) -> Bool
	| Plus(e1, e2) -> type_checker_PlusAndMul gamma e1 e2									
	| Multiplication(e1, e2) -> type_checker_PlusAndMul gamma e1 e2			
	| Pair(e1,e2) -> Times(typ1,typ2)
	| First(e) -> match type_checker gamma e with 
					| Times(typ1,typ2) -> typ1
					|_ ->raise(Failure "Type check for First fails") 
	| Second(e) -> match type_checker gamma e with 
					| Times(typ1,typ2) -> typ2
					|_ ->raise(Failure "Type check for First fails") 
	| Ref(e) -> 	RefT(type_checker gamma e)			
	| Deref(e) -> match type_checker gamma e with 
				| typ1 -> RefT(typ1) 
	| Assignment(e1,e2) ->  match type_checker gamma e1 with 
										|RefT (typ1) -> type_checker gamma e2
										|_-> raise(Failure "Type check for Assignment fails")	
	|Match(e, list(pattern,body)) -> type_checker_Match gamma e list(pattern,body)
											
	
	(*Type checker for App(e1,e2) *)
	and type_checker_App gamma e1 e2 =  match type_checker gamma e1 with 
										|Fun (typ1,typ2) -> if (subtyping (type_checker gamma e2) t1) then t2
										|_-> raise(Failure "Type check for App fails")
	
	(*Type checnker for Plus(e1,e2) and Multiplication(e1,e2) *)
	and type_checker_PlusAndMul gamma e1 e2 = 
	if type_checker gamma e1 = IntT 
		then begin
			if subtyping (type_checker gamma e2) FloatT then IntT 
			end 
	else if type_checker gamma e1 = FloatT then FloatT
	else raise(Failure "Typecheck for either Plus or Multiplication failed")
	
	(*Type checnker for If(e1,e2,e3)*)
	and type_checker_If gamma e1 e2 e3 = 
		if type_checker gamma e1 = Bool 
			then begin
				let t2 = type_checker gamma e2 in 
				if t2 = (subtyping (type_checker gamma e3) t2) then t2
		    		else raise(Failure "Branches of If must have same type")
		  	end
	  	else raise(Failure "Guard of if must have type bool") 
	(*Type checker for Match(e, clause) *)				
	and	type_checker_Match gamma e list(pattern,body) = 
	if type_checker gamma e = T && type_checker gamma pattern = T 
		then begin 
			let GammaPrime = (type_checker gamma list(pattern)) in
			match pattern  with 
			| TrueP ->if type_checker gamma TrueP Bool then  GammaPrime = []
			| IntP -> if type_checker gamma IntP IntT then GammaPrime = []
			| VarP(typ, varname) -> if type_checker gamma VarP Fun(t1,string) GammaPrime = Pair(t1, binding)
			| PairP(p1,p2) -> if t1 = type_checker gamma p1 t1 then GammaPrime = Pair(t1, binding1) 
							 and if t2 = type_checker gamma p2 in then GammaDoublePrime = Pair(t1, binding1) 
							 and if PairT(t1,t2) = type_checker gamma PairP(p1,p2) then Pair(GammaPrime,GammaDoublePrime)
								
							 
			

let main = print_string (prettyPrinter_exp_ln(evaluator (First( Pair(True,False) ))));
		print_string "\n";
		(*
			print_string (prettyPrinter_exp_ln (If(True, (App(Lambda("x", Bool , Var("x")), True)), False)));
		   print_string (prettyPrinter_exp_ln (evaluator (If(True, (App(Lambda("x", Int , Var("x")), True)), False))));
		   print_string (prettyPrinter_exp_ln (If(False, Lambda("x", Bool, Var("x")), Lambda("z", Bool, App(Var("z"), Var("z"))))));
		   print_string "Result: \n";
		   print_string (prettyPrinter_exp_ln (evaluator (If(False, Lambda("x", Bool, Var("x")), Lambda("z", Bool, App(Var("z"), Var("z")))))));
*)
