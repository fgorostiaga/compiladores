open tigertab
open tigertemp
open tigergraph
open tigerflow
open tigerassem
fun instrs2graph inss =
	let fun getLabelNode lab graph labs = (case tabBusca (lab,labs) of
											SOME n => (n,labs)
											|NONE => let val mynode = newNode graph
														val labs = tabInserta(lab,mynode,labs)
														in (mynode,labs) end)

		fun aux graph nodelist [] _ _ = (graph, List.rev nodelist)
			|aux (FGRAPH {control, def, use, ismove}) nodelist (OPER {assem, dst, src, jump = SOME js} :: rest) tablaLabels maybelastnode =
					let val mynode = newNode control
						val _ = (case maybelastnode of SOME lastnode => mk_edge {from = lastnode, to = mynode}
														|NONE => ())
						(*Se crean edges hacia los jumps*)
						val tablaLabels = (case js of [lab] => let val (labnode, tablaLabels) = getLabelNode lab control tablaLabels
																			val _ = mk_edge {from = mynode, to = labnode}
							 											in tablaLabels end
														|[lab0, lab1] => let val (labnode, tablaLabels) = getLabelNode lab0 control tablaLabels
																			val _ = mk_edge {from = mynode, to = labnode}
                                                                            val (labnode, tablaLabels) = getLabelNode lab1 control tablaLabels
																			val _ = mk_edge {from = mynode, to = labnode}
							 											in tablaLabels end
														| [] => raise Fail ("SOME 0 jumps. Assem: "^assem)
														| _ => raise Fail "More than 2 jumps? Not on MY watch.")
						val nodelist = (mynode :: nodelist)
						val def = tabRInserta (mynode, dst, def)
						val use = tabRInserta (mynode, src, use)
						val ismove = tabRInserta (mynode, false, ismove)
					in aux (FGRAPH {control=control, def=def, use=use, ismove=ismove}) nodelist rest tablaLabels NONE
					end
			|aux (FGRAPH {control, def, use, ismove}) nodelist (OPER {assem, dst, src, jump = NONE} :: rest) tablaLabels maybelastnode =
					let val mynode = newNode control
						val _ = (case maybelastnode of SOME lastnode => mk_edge {from = lastnode, to = mynode}
														|NONE => ())
						val nodelist = (mynode :: nodelist)
						val def = tabRInserta (mynode, dst, def)
						val use = tabRInserta (mynode, src, use)
						val ismove = tabRInserta (mynode, false, ismove)
					in aux (FGRAPH {control=control, def=def, use=use, ismove=ismove}) nodelist rest tablaLabels (SOME mynode)
					end
			|aux (FGRAPH {control, def, use, ismove}) nodelist (LABEL {assem, lab} :: rest) tablaLabels maybelastnode =
					let val (mynode, tablaLabels) = getLabelNode lab control tablaLabels
						val _ = (case maybelastnode of SOME lastnode => mk_edge {from = lastnode, to = mynode}
														|NONE => ())
						val nodelist = (mynode :: nodelist)
						val def = tabRInserta (mynode, [], def)
						val use = tabRInserta (mynode, [], use)
						val ismove = tabRInserta (mynode, false, ismove)
					in aux (FGRAPH {control=control, def=def, use=use, ismove=ismove}) nodelist rest tablaLabels (SOME mynode)
					end
			|aux (FGRAPH {control, def, use, ismove}) nodelist (MOVE {assem, dst, src} :: rest) tablaLabels maybelastnode =
					let val mynode = newNode control
						val _ = (case maybelastnode of SOME lastnode => mk_edge {from = lastnode, to = mynode}
														|NONE => ())
						val nodelist = (mynode :: nodelist)
						val def = tabRInserta (mynode, [dst], def)
						val use = tabRInserta (mynode, [src], use)
						val ismove = tabRInserta (mynode, true, ismove)
					in aux (FGRAPH {control=control, def=def, use=use, ismove=ismove}) nodelist rest tablaLabels (SOME mynode)
					end
in
	aux (FGRAPH {control = newGraph (),
				def = tabNueva (),
				use= tabNueva (),
				ismove= tabNueva ()}) [] inss (tigertab.tabNueva ()) NONE
end
