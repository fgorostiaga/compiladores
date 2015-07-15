signature tigercodegen = 
sig
	structure Frame : tigerframe
	val codegen : Frame.frame -> Tree.stm -> Assem.instr list
end
