open Splayset
open tigerflow
open tigertab
open Array
fun livenessAnalisis (FGRAPH {control, def, use, ismove}, nodeList) : ((node, string set) Tabla * (node, string set) Tabla) =

(* Faaa que animal feliii *)
	let 

		fun tabBuscaDefaults (rtabla, clave, default) = case tabBusca (clave, !rtabla) of SOME x=>x
																					| NONE => (rtabla := tabRInserta(clave, default, !rtabla); default)

		fun getuse node = let 
								val uses = (case tabBusca (node, use) of SOME x=> x | NONE => [])
							in addList (empty String.compare, uses) end
		fun getdef node = let
								val defs = (case tabBusca (node, def) of SOME x=> x | NONE => [])
							in addList (empty String.compare, defs) end

		val emptystring = empty String.compare

		val instab = ref (tabNueva ())
		val outstab = ref (tabNueva ())

		fun updateTables n = let val insn' = tabBuscaDefaults(instab, n, emptystring)
								val outsn' = tabBuscaDefaults(outstab, n, emptystring)
								val _ = instab := tabRInserta(n, union(getuse n, difference(outsn', getdef n)), !instab)
								val _ = outstab := tabRInserta(n, List.foldl (fn (node,set) => union (set, tabBuscaDefaults(instab,node, emptystring))) (emptystring) (tigergraph.succ n), !outstab)
							in equal(insn', tabBuscaDefaults(instab,n, emptystring)) andalso equal(outsn', tabBuscaDefaults(outstab,n, emptystring)) end

		fun iterate () = (print "iterating!\n"; if List.foldl (fn (n,res) => updateTables n andalso res) true nodeList then (print "aut!\n") else iterate ())

	in (iterate ();(!instab, !outstab)) end
