open tigerliveness
open tigertab
open tigertemp
open tigergraph
open tigerflow
open Splayset

val adjSet = ref (empty (fn ((u0,v0),(u1,v1)) => if u0=u1 then String.compare(v0,v1) else String.compare(u0,u1)))
val adjList = ref (tabNueva ())
val degree = ref (tabNueva ())
val precolored = [tigerframe.fp]

fun listmember _ [] = false
	|listmember x (y::rest) = if x=y then true else listmember x rest

fun tabBuscaDefaults (tabla, clave, default) = case tabBusca(clave,tabla) of SOME x => x | NONE => default

fun addEdge(u,v) =
	if member(!adjSet, (u,v)) orelse u=v then () else (
		adjSet := (addList(!adjSet,[(u,v),(v,u)]));
		if listmember u precolored then () else (
				adjList := (tabRInserta(u, add(tabBuscaDefaults(!adjList,u,empty String.compare),v),!adjList));
				degree := (tabRInserta(u,tabBuscaDefaults(!degree,u,0)+1,!degree))
		);
		if listmember v precolored then () else (
				adjList := (tabRInserta(v, add(tabBuscaDefaults(!adjList,v,empty String.compare),u),!adjList));
				degree := (tabRInserta(v,tabBuscaDefaults(!degree,v,0)+1,!degree))
		)
	)


fun build (FGRAPH {control, def, use, ismove}) nodes outsarray =
	let
		val _ = adjSet := (empty (fn ((u0,v0),(u1,v1)) => if u0=u1 then String.compare(v0,v1) else String.compare(u0,u1)))
		val _ = adjList := (tabNueva ())
		val _ = degree := (tabNueva ())

		fun findInTab(x,tab) = case tabBusca(x,tab) of SOME s=>addList(empty String.compare,s) | NONE => raise Fail "Nodo no encontrado"

		fun aux [] moveList worklistMoves _ = (moveList, worklistMoves)
			|aux (instr :: rest) moveList worklistMoves i =
				let val live = sub(outsarray, i)
					val (live, moveList, worklistMoves) = case tabBusca(instr,ismove) of
						SOME false => (live,moveList,worklistMoves)
						|SOME true => let val useI = findInTab(instr,use)
											val defI = findInTab(instr,def)
											val live = difference(live,useI)
											val deforuseI = union(useI,defI)
											val moveList = foldl (fn (item,tabla) => tabRInserta(item,tabBuscaDefaults(tabla,item,empty String.compare),tabla)) moveList deforuseI
											val worklistMoves = add(worklistMoves,instr)
										in (live,moveList,worklistMoves) end
						|NONE => raise Fail "nodo no encontrado en ismove"
					val defsinstr = findInTab(instr,def)
					val live = union(live, defsinstr)
					val _ = app (fn d => app (fn l => addEdge(l,d)) live) defsinstr
				in aux rest moveList worklistMoves (i+1) end

	in aux nodes (tabNueva ()) (empty compare) 0 end

fun main fgraph nodes = 
	let val (insarray, outsarray) = livenessAnalisis (fgraph, nodes)
		val (moveList, worklistMoves) = build fgraph nodes outsarray
	in (insarray,outsarray, !adjList) end
