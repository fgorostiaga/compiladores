signature tigergraph =
sig
	type graph
	eqtype node

	val nodes : graph -> node list
	val succ : node -> node list
	val pred : node -> node list
	val adj : node -> node list
	val eq : node*node -> bool
	val compare : node*node -> order

	val newGraph : unit -> graph
	val newNode : graph -> node
	exception GraphEdge
	val mk_edge : {from:node, to:node} -> unit
	val rm_edge : {from:node, to:node} -> unit

	type 'a Table = (node, 'a) tigertab.Tabla
	val nodeTabNueva : unit -> (node, 'a) tigertab.Tabla

	val nodename : node -> string (*For debugging*)
end
