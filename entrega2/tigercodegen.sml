

fun codegen (frame) (stm: Tree.stm) : Assem.instr list = 

let val ilist = ref (nil: A.instr list)
	fun emit x = ilist := x :: !ilist
	fun result(gen) = let val t = Temp.newtemp() in gen t; t end
	(* munchStm::Tree.stm -> unit *)
	and munchStm ...
	(* munchExp::Tree.exp -> Temp.temp *)
	fun munchExp ... 

in munchStm stm;
	rev(!ilist)
end
