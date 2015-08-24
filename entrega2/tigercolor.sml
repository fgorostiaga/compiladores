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

fun tabBuscaDefaults (tabla, valor, default) = case tabBusca(valor,tabla) of SOME x => x | NONE => default

fun addEdge(u,v) =
	if member(!adjSet, (u,v)) orelse u=v then () else (
		adjSet := (addList(!adjSet,[(u,v),(v,u)]));
		if listmember u precolored then () else (
				adjList := (tabRInserta(u, addList(tabBuscaDefaults(!adjList,u,empty String.compare),[v]),!adjList));
				degree := (tabRInserta(u,tabBuscaDefaults(!degree,u,0)+1,!degree))
		);
		if listmember v precolored then () else (
				adjList := (tabRInserta(v, addList(tabBuscaDefaults(!adjList,v,empty String.compare),[u]),!adjList));
				degree := (tabRInserta(v,tabBuscaDefaults(!degree,v,0)+1,!degree))
		)
	)


fun build (FGRAPH {control, def, use, ismove}) nodes outsarray =
	let
		val _ = adjSet := (empty (fn ((u0,v0),(u1,v1)) => if u0=u1 then String.compare(v0,v1) else String.compare(u0,u1)))
		val _ = adjList := (tabNueva ())
		val _ = degree := (tabNueva ())

		fun getDefs n = case tabBusca(n,def) of SOME x => addList(empty String.compare,x) | NONE => raise Fail "nodo no encontrado en def"

		fun aux [] moveList worklistMoves _ = (moveList, worklistMoves)
			|aux (instr :: rest) moveList worklistMoves i =
				let val live = sub(outsarray, i)
					val (live, moveList, worklistMoves) = (live,moveList,worklistMoves)
					val defsinstr = getDefs instr
					val live = union(live, defsinstr)
					val _ = app (fn d => app (fn l => addEdge(l,d)) live) defsinstr
				in aux rest moveList worklistMoves (i+1) end

	in aux nodes (tabNueva ()) (empty compare) 0 end

fun main fgraph nodes = 
	let val (insarray, outsarray) = livenessAnalisis (fgraph, nodes)
		val (moveList, worklistMoves) = build fgraph nodes outsarray
	in (insarray,outsarray, !adjList) end
