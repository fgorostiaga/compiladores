

fun codegen (frame) (stm: Tree.stm) : Assem.instr list = 

let val ilist = ref (nil: A.instr list)
	fun emit x = ilist := x :: !ilist
	fun result(gen) = let val t = Temp.newtemp() in gen t; t end
	(* munchStm::Tree.stm -> unit *)
	fun munchStm(SEQ(a, b)) = (munchStm a; munchStm b)(*primer stm*)
	(*comenzamos por el final, para ir de los arboles mas simples a los mas complejos. Feli dice: no es al reves? Ir de los mas complejos a los mas simples?*)
	|   munchStm(MOVE(TEMP i,BINOP(PLUS,MEM(CONST j),e1))) = 
		emit(OPER{assem = "MOV 'd0, " ^ int j ^ "["^e1^"]\n"
			  dst = [i],
			  src = [munchExp(e1)],
			  jump = NONE}) 
	|   munchStm(MOVE(TEMP i, e1)) =
		emit(OPER{assem = "MOV 'd0, 's0 \n"
			  dst = [i],
			  src = [munchExp(e1)]
			  jump = NONE}) 
	|   munchStm(MOVE(TEMP i, CONST j)) = 
		emit(OPER{assem = "MOV 'd0, " ^ int i ^ " \n", 
			  dst = [i],
			  src = [],
			  jump = NONE})
	|   munchStm(LABEL lab ) = 
		emit(OPER{assem = lab ^ ": \n", lab=lab }) 
	(* munchStm::Tree.stm -> unit *)
	and(*comenzamos por las exp mas simples, que van "abajo" en el pattern matching*)
	(* munchExp::Tree.exp -> Temp.temp *)

	 munchExp(CONST i) = (*no estoy seguro de esta. 'd0 deberia tener 0*)
		result(fn r => emit(OPER{assem = "ADD 'd0, "^int i^" \n"
			src = [],
			dst = [r],
			jump = NONE})) 
	|    munchExp(BINOP(MINUS,e1,e2)) =
		result(fn r => emit(OPER{assem = "SUB 'd0 's0",
			src = [munchExp(e1), munchExp(e2)],
			dst = [r],
			jump = NONE}))
	|    munchExp(BINOP(DIV,e1,e2)) =
		result(fn r => emit(OPER{assem = "DIV 'd0 's0",
			src = [munchExp(e1), munchExp(e2)],
			dst = [r],
			jump = NONE}))
	|    munchExp(BINOP(MUL,e1,e2)) =
		result(fn r => emit(OPER{assem = "MUL 'd0 's0",
			src = [munchExp(e1), munchExp(e2)],
			dst = [r],
			jump = NONE}))
	|    munchExp(BINOP(PLUS,e1,e2)) =
		result(fn r => emit(OPER{assem = "ADD 'd0 's0",
			src = [munchExp(e1), munchExp(e2)],
			dst = [r],
			jump = NONE})  )
	|    munchExp(TEMP t) = t
	     

in munchStm stm;
	rev(!ilist)
end
