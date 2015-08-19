	type node = tigergraph.node
	datatype flowgraph =
		FGRAPH of {control: tigergraph.graph,
				def: tigertemp.temp list tigergraph.Table,
				use: tigertemp.temp list tigergraph.Table,
				ismove: bool tigergraph.Table}
