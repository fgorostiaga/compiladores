structure tigertree =
struct
	datatype exp = CONST of int
		     | NAME of tigertemp.label
		     | TEMP of tigertemp.temp
		     | BINOP of binop*exp*exp
		     | MEM of exp
		     | CALL of exp*exp list
		     | ESEQ of stm*exp
	and stm = MOVE of exp*exp
		| EXP of exp
		| JUMP of exp*tigertemp.label list
		| CJUMP of relop*exp*exp*tigertemp.label*tigertemp.label
		| SEQ of stm*stm
		| LABEL of tigertemp.label
	and binop = PLUS | MINUS | MUL | DIV | AND | OR
		  | LSHIFT | RSHIFT | ARSHIFT | XOR
	and relop = EQ | NE | LT | GT | LE | GE | ULT | ULE
		  | UGT | UGE

	fun notRel EQ = NE
	  | notRel NE = EQ
	  | notRel LT = GE
	  | notRel GE = LT
	  | notRel GT = LE
	  | notRel LE = GT
	  | notRel ULT = UGE
	  | notRel UGE = ULT
	  | notRel ULE = UGT
	  | notRel UGT = ULE


	fun ppSTM (MOVE (e1, e2)) = "MOVE e1: (" ^ (ppEXP e1) ^ "), e2: (" ^ (ppEXP e2) ^ ")"
		| ppSTM (EXP e) = "EXP e: (" ^ (ppEXP e) ^ ")"
		| ppSTM (JUMP (e, labels)) = "JUMP e:(" ^ (ppEXP e) ^ "), [list of labels!]"
		| ppSTM (CJUMP (ope, e1, e2, l1, l2)) = "CJUMP operation: (" ^ (ppRELOP ope) ^ "), e1:(" ^ (ppEXP e1) ^ ") will jump to: " ^ (ppLABEL l1) ^ ", e2: (" ^ (ppEXP e2) ^ ") will jump to: " ^ (ppLABEL l2) 
		| ppSTM (SEQ (stm1, stm2)) = "SEQ stm1: (" ^ (ppSTM stm1) ^ "), stm2: (" ^ (ppSTM stm2) ^ ")"
		| ppSTM (LABEL l) = "LABEL: " ^ (ppLABEL l)

	and ppEXP (CONST i) = "CONST " ^ (Int.toString i)
		| ppEXP (NAME l) = "NAME " ^ (ppLABEL l)
		| ppEXP (TEMP temp) = "TEMP algo"
		| ppEXP (BINOP (b, e1, e2)) = "BINOP b: " ^ (ppBINOP b) ^ ", e1: " ^ (ppEXP e1) ^ ", e2: " ^ (ppEXP e2)
		| ppEXP (MEM e) = "MEM e: " ^ (ppEXP e)
		| ppEXP (CALL (e, es)) = "CALL e: " ^ (ppEXP e) ^ "es: algos"
		| ppEXP (ESEQ (s, e)) = "ESEQ s: (" ^ (ppSTM s) ^ "), e: (" ^ (ppEXP e) ^ ")"

	and ppRELOP EQ = "EQ"
		| ppRELOP NE = "NE"
		| ppRELOP LT = "LT"
		| ppRELOP GT = "GT"
		| ppRELOP LE = "LE"
		| ppRELOP GE = "GE"
		| ppRELOP ULT = "ULT"
		| ppRELOP ULE = "ULE"
		| ppRELOP UGT = "UGT"
		| ppRELOP UGE = "UGE"

	and ppBINOP PLUS = "PLUS"
		| ppBINOP MINUS = "MINUS"
		| ppBINOP MUL = "MUL"
		| ppBINOP DIV = "DIV"
		| ppBINOP AND = "AND"
		| ppBINOP OR = "OR"
		| ppBINOP LSHIFT = "LSHIFT"
		| ppBINOP RSHIFT = "RSHIFT"
		| ppBINOP ARSHIFT = "ARSHIFT"
		| ppBINOP XOR = "XOR"

	and ppLABEL l = l
end
