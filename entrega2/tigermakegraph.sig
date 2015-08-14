signature tigermakegraph =
sig
	val instrs2graph: tigerassem.instr list -> tigerflow.flowgraph * tigerflow.node list
end
