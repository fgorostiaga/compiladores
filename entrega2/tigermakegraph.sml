open tigertab
open tigertemp
open tigergraph
fun instrs2graph ins = (tigerflow.FGRAPH {control = newGraph (),
											def = tabNueva (),
											use= tabNueva (),
											ismove= tabNueva ()},[])
