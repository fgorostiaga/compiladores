open Array
open Splayset
open tigerflow
open tigertab
fun livenessAnalisis (FGRAPH {control, def, use, ismove}, nodeList) : (tigertemp.temp set array * tigertemp.temp set array) =

(* Faaa que animal feliii *)
	let 
		fun getuse index = let val mynode = List.nth (nodeList, index)
								val uses = (case tabBusca (mynode, use) of SOME x=> x | NONE => [])
							in addList (empty String.compare, uses) end
		fun getdef index = let val mynode = List.nth (nodeList, index)
								val defs = (case tabBusca (mynode, def) of SOME x=> x | NONE => [])
							in addList (empty String.compare, defs) end

		val listlen = List.length nodeList
		val insarray = tabulate (listlen, fn _ => empty String.compare)
		val outsarray = tabulate (listlen, fn _ => empty String.compare)

		fun findNodeIndex node = let fun aux [] _ = raise Fail "Node not found!"
										|aux (n'::rest) i = if tigergraph.eq(node,n') then i else aux rest (i+1)
								in aux nodeList 0 end

		fun getSuccsIndexes index = let val mynode = List.nth (nodeList, index)
										val succesorNodes = tigergraph.succ mynode
									in List.map findNodeIndex succesorNodes end

		fun updateArrays n = let val insn' = sub(insarray,n)
								val outsn' = sub(outsarray,n)
								val _ = update(insarray, n, union(getuse n, difference(outsn', getdef n)))
								val _ = update(outsarray, n, List.foldl (fn (index,set) => union (set, sub(insarray,index))) (empty String.compare) (getSuccsIndexes n))
							in equal(insn', sub(insarray,n)) andalso equal(outsn', sub(outsarray,n)) end

		fun iterate () = if List.foldl (fn (i,res) => updateArrays i andalso res) true (List.tabulate (listlen, (fn x=>x))) then () else iterate ()

	in (iterate ();(insarray, outsarray)) end
