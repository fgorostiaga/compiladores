open tigerliveness
open tigertab
open tigertemp
open tigergraph
open tigerflow
open Splayset

val adjSet = ref (empty (fn ((u0,v0),(u1,v1)) => if u0=u1 then String.compare(v0,v1) else String.compare(u0,u1)))
val adjList = ref (tabNueva ())
val degree : (tigertemp.temp , int) Tabla ref = ref (tabNueva ())
val moveList = ref (tabNueva())
val worklistMoves = ref (empty compare)
val activeMoves = ref (empty compare)
val spillWorklist = ref (empty String.compare)
val freezeWorklist = ref (empty String.compare)
val simplifyWorklist = ref (empty String.compare)
val precolored = [tigerframe.fp]
val k = 5

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
		val _ = moveList := (tabNueva())
		val _ = worklistMoves := (empty compare)
		val _ = activeMoves := (empty compare)

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
											val moveList = foldl (fn (item,tabla) => tabRInserta(item,tabBuscaDefaults(tabla,item,empty compare),tabla)) moveList deforuseI
											val worklistMoves = add(worklistMoves,instr)
										in (live,moveList,worklistMoves) end
						|NONE => raise Fail "nodo no encontrado en ismove"
					val defsinstr = findInTab(instr,def)
					val live = union(live, defsinstr)
					val _ = app (fn d => app (fn l => addEdge(l,d)) live) defsinstr
				in aux rest moveList worklistMoves (i+1) end

	in aux nodes (!moveList) (!worklistMoves) 0 end

fun nodeMoves n = intersection(tabBuscaDefaults(!moveList,n,empty compare),union(!activeMoves,!worklistMoves))

fun moveRelated n = not (isEmpty(nodeMoves n))

fun makeWorklist () = let val initial = tigerframe.argregs @ (tigerframe.fp :: List.tabulate(tigertemp.lastTempIndex (), fn(i)=>"T"^Int.toString(i)))
							fun aux [] tr = tr
								|aux (n::rest) (spwl,fwl,siwl) =
									let 
										val degreen = tabBuscaDefaults(!degree,n,~1)
										val (spwl,fwl,siwl) = if (degreen<0) then (spwl,fwl,siwl) else if degreen >= k then
											(add(spwl,n),fwl,siwl) else if moveRelated n then
												(spwl,add(fwl,n),siwl) else
												(spwl,fwl,add(siwl,n))
									in aux rest (spwl,fwl,siwl) end
							in aux initial (empty String.compare,empty String.compare,empty String.compare) end

fun main fgraph nodes = 
	let val (insarray, outsarray) = livenessAnalisis (fgraph, nodes)
		val (a,b) = build fgraph nodes outsarray
		val _ = (moveList := a; worklistMoves := b)
		val (a, b, c) = makeWorklist ()
		val _ = (spillWorklist := a; freezeWorklist :=b; simplifyWorklist:=c)
		fun iterate () = if isEmpty(!simplifyWorklist) andalso isEmpty(!worklistMoves) andalso isEmpty(!freezeWorklist) andalso isEmpty(!spillWorklist) then () else ()
		val _ = iterate ()
	in (insarray,outsarray, !adjList) end
