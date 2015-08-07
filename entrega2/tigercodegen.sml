
open tigertree
open tigerassem
open tigerframe

fun codegen2 frags =

let fun codegen (stm: tigertree.stm) : tigerassem.instr list =  (*Saque el argumento frame porque tenemos FP. Referirse a pagina 206 del Appel para mas detalles. Gracias, vuelva prontos.*)

let val ilist = ref (nil: tigerassem.instr list)
	fun emit x = ilist := x :: !ilist
	fun result(gen) = let val t = tigertemp.newtemp() in gen t; t end
	(* munchStm::Tree.stm -> unit *)
	fun munchStm(SEQ(a, b)) = (munchStm a; munchStm b)(*primer stm*)
	(*comenzamos por el final, para ir de los arboles mas simples a los mas complejos. Feli dice: no es al reves? Ir de los mas complejos a los mas simples?*)
	|	munchStm (EXP(CALL (NAME n,args))) = (*Procedure*)
			emit(OPER{assem="CALL "^n^"\n",
						src=munchArgs (List.rev args),
						dst=argregs,
						jump=NONE})
	|	munchStm (tigertree.MOVE(TEMP i, TEMP j)) =
			emit(MOVE{assem = "MOV 'd0, 's0\n",
					dst = i,
					src = j})
	|	munchStm (tigertree.MOVE(TEMP i,CALL (NAME n,args))) = (*Function call*)
			(munchStm(EXP(CALL(NAME n,args)));
			emit(MOVE{assem = "MOV 'd0, 's0 \n",
				  dst = i,
				  src = rv}))
	|   munchStm(tigertree.MOVE(TEMP i,BINOP(PLUS,MEM(CONST j),e1))) =  (*Por que esta este "MEM"? El pattern no deberia matchear mas bien con MOVE (TEMP i, BINOP(PLUS,CONST j, MEM(m))) ? *)
		emit(MOVE{assem = "MOV 'd0, " ^(Int.toString j) ^ "['s0]\n", (*La forma no deberia ser MOV 'd0, j('s0)?*)
			  dst = i,
			  src = munchExp(e1)})
	|   munchStm(tigertree.MOVE(TEMP i, CONST j)) = 
		emit(OPER{assem = "MOV 'd0, " ^ (Int.toString j) ^ " \n", (*Hay que cambiar los OPER por MOVE cuando sea necesario. Aca, por ejemplo, no lo es. ;P*)
			  dst = [i],
			  src = [],
			  jump = NONE})
	|   munchStm(tigertree.MOVE(TEMP i, e1)) =
		emit(OPER{assem = "MOV 'd0, 's0 \n",
			  dst = [i],
			  src = [munchExp(e1)],
			  jump = NONE}) 
	|   munchStm(tigertree.MOVE(MEM e0, e1)) =
		emit(OPER{assem = "MOV ['d0], 's0 \n",
			  dst = [munchExp e0],
			  src = [munchExp(e1)],
			  jump = NONE}) 
	|   munchStm(JUMP(NAME e,lls)) =	
		emit(OPER{assem = "JMP 'j0 \n",
			  dst = [],
			  src = [],
			  jump = SOME [e]})
	|   munchStm(CJUMP(EQ,e1,e2,l1,l2)) =
		emit(OPER{assem = "CMP 's0 's1 \n"
				  ^ "JE 'j0 \n",
			  dst = [],
			  src = [munchExp(e1),munchExp(e2)],
			  jump = SOME [l1,l2]})
	|   munchStm(CJUMP(NE,e1,e2,l1,l2)) =	
		emit(OPER{assem = "CMP 's0 's1 \n"
				  ^ "JNE 'j0 \n",
			  src = [munchExp(e1),munchExp(e2)],
			  dst = [],
			  jump = SOME [l1,l2]})
	|   munchStm(CJUMP(LT,e1,e2,l1,l2)) =	
		emit(OPER{assem = "CMP 's0 's1 \n"
				  ^ "JL 'j0 \n",
			  src = [munchExp(e1),munchExp(e2)],
			  dst = [],
			  jump = SOME [l1,l2]})

	|   munchStm(CJUMP(GT,e1,e2,l1,l2)) =	
		emit(OPER{assem = "CMP 's0 's1 \n"
				  ^ "JG 'j0 \n",
			  src = [munchExp(e1),munchExp(e2)],
			  dst = [],
			  jump = SOME [l1,l2]})

	|   munchStm(CJUMP(LE,e1,e2,l1,l2)) =	
		emit(OPER{assem = "CMP 's0 's1 \n"
				  ^ "JLE 'j0 \n",
			  src = [munchExp(e1),munchExp(e2)],
			  dst = [],
			  jump = SOME [l1,l2]})
	|   munchStm(CJUMP(GE,e1,e2,l1,l2)) =	
		emit(OPER{assem = "CMP 's0 's1 \n"
				  ^ "JGE 'j0 \n",
			  src = [munchExp(e1),munchExp(e2)],
			  dst = [],
			  jump = SOME [l1,l2]})
	|   munchStm(CJUMP(ULT,e1,e2,l1,l2)) =	
		emit(OPER{assem = "CMP 's0 's1 \n"
				  ^ "JB 'j0 \n",
			  src = [munchExp(e1),munchExp(e2)],
			  dst = [],
			  jump = SOME [l1,l2]})
	|   munchStm(CJUMP(ULE,e1,e2,l1,l2)) =	
		emit(OPER{assem = "CMP 's0 's1 \n"
				  ^ "JBE 'j0 \n",
			  src = [munchExp(e1),munchExp(e2)],
			  dst = [],
			  jump = SOME [l1,l2]})
	|   munchStm(CJUMP(UGT,e1,e2,l1,l2)) =	
		emit(OPER{assem = "CMP 's0 's1 \n"
				  ^ "JA 'j0 \n",
			  src = [munchExp(e1),munchExp(e2)],
			  dst = [],
			  jump = SOME [l1,l2]})
	|   munchStm(CJUMP(UGE,e1,e2,l1,l2)) =	
		emit(OPER{assem = "CMP 's0 's1 \n"
				  ^ "JAE 'j0 \n",
			  src = [munchExp(e1),munchExp(e2)],
			  dst = [],
			  jump = SOME [l1,l2]})
	|   munchStm(tigertree.LABEL lab ) = 
		emit(LABEL{assem = lab ^ ": \n", lab=lab }) 
	|   munchStm(EXP(e)) = 
		emit(MOVE{assem = "MOV 'd0, 's0 \n",
			  dst = tigertemp.newtemp(),
			  src = munchExp(e)})
	|	munchStm _ = emit (OPER{assem = "nada.\n",
				src	 = [], dst = [], jump = NONE})
	(* munchStm::Tree.stm -> unit *)
	and(*comenzamos por las exp mas simples, que van "abajo" en el pattern matching*)
	(* munchExp::Tree.exp -> tigertemp.temp *)

	 munchExp(CONST i) = (*no estoy seguro de esta. 'd0 deberia tener 0*)
		result(fn r => emit(OPER{assem = "MOV 'd0, "^(Int.toString i)^" \n",
			src = [],
			dst = [r],
			jump = NONE})) 
	|    munchExp(BINOP(MINUS,e1,e2)) =
		result(fn r => emit(OPER{assem = "MOV 'd0 's0\nSUB 'd0 's1\n",
			src = [munchExp(e1), munchExp(e2)],
			dst = [r],
			jump = NONE}))
	|    munchExp(BINOP(DIV,e1,e2)) =
		result(fn r => emit(OPER{assem = "MOV 'd0 's0\nDIV 'd0 's1\n",
			src = [munchExp(e1), munchExp(e2)],
			dst = [r],
			jump = NONE}))
	|    munchExp(BINOP(MUL,e1,e2)) =
		result(fn r => emit(OPER{assem = "MOV 'd0 's0\nMUL 'd0 's1\n",
			src = [munchExp(e1), munchExp(e2)],
			dst = [r],
			jump = NONE}))
	|    munchExp(BINOP(PLUS,e1,e2)) =
		result(fn r => emit(OPER{assem = "MOV 'd0 's0\nADD 'd0 's1\n",
			src = [munchExp(e1), munchExp(e2)],
			dst = [r],
			jump = NONE})  )
	|    munchExp(TEMP t) = t
	|	munchExp (MEM e) = result (fn r=> emit(OPER{assem="MOV 'd0 ['s0]\n",
													dst = [r],
													src = [munchExp e],
													jump = NONE}))
	|	munchExp (NAME l) = result (fn r=> emit(OPER{assem="MOV 'd0 $"^l^"\n",
														dst=[r],
														src=[],
														jump=NONE}))
	|	munchExp exp = result (fn r=>emit(OPER{assem="NADA: "^(ppEXP exp)^"\n",src=[], dst=[], jump=NONE}))

	and munchArgs [] = []
		|munchArgs(arg::args) = let val temp = munchExp(arg)
										in (case (getArgForPos (List.length args)) of
														InReg reg => (emit(MOVE {assem = "MOV 'd0, 's0\n",
																				dst = reg,
																				src = temp})														
																	;(reg :: munchArgs args))
														|InFrame offset => (emit(OPER {assem = "PUSHQ 's0\n",
																						dst = [],
																						src = [temp],
																						jump = NONE})
																			;munchArgs args)
	     											)
									end

in munchStm stm;
	rev(!ilist)
end
		fun aux2(PROC{body, frame}) = codegen body
		| aux2(STRING(l, "")) = [(LABEL{assem = l ^ ": \n", lab=l })]
		| aux2(STRING(l, s)) = [(LABEL{assem = l^":\t"^s^"\n", lab=l })]
		fun aux3 [] = []
		| aux3(h::t) = (aux2 h)@(aux3 t)
	in	aux3 frags end
