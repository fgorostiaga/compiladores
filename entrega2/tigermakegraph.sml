open tigertab
open tigertemp
open tigergraph
open tigerflow
fun instrs2graph inss =
	let fun aux graph nodelist [] _ _ = (graph, List.rev nodelist)
			|aux (FGRAPH {control, def, use, ismove}) nodelist (inst :: rest) tablaLabels maybelastnode =
					let val mynode = newNode control (*Si es label, buscarlo en la tabla, y actualizarla de ser necesario*)
						val _ = (case maybelastnode of SOME lastnode => mk_edge {from = lastnode, to = mynode}
														|NONE => ())
						(*Seguir creando edges si hay jumps*)
						val nodelist = (mynode :: nodelist)
						val def = tabRInserta (mynode, [], def)
						val use = tabRInserta (mynode, [], use)
						val ismove = tabRInserta (mynode, (*depende*)false, ismove)
					in aux (FGRAPH {control=control, def=def, use=use, ismove=ismove}) nodelist rest tablaLabels (SOME mynode (*Siempre, a menos que sea un JUMP incondicional*))
					end
in
	aux (FGRAPH {control = newGraph (),
				def = tabNueva (),
				use= tabNueva (),
				ismove= tabNueva ()}) [] inss (tabNueva ()) NONE
end
