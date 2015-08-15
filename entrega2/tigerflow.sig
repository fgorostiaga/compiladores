signature tigerflow =
sig
	type node = tigergraph.node
	datatype flowgraph =
		FGRAPH of {control: tigergraph.graph,
				def: tigertemp.temp tigergraph.Table,
				use: tigertemp.temp tigergraph.Table,
				ismove: bool tigergraph.Table}
end
