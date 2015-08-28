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
val constrainedMoves = ref (empty compare)
val coalescedMoves = ref (empty compare)
val selectStack = ref []
val coalescedNodes = ref (empty String.compare)
val spillWorklist = ref (empty String.compare)
val freezeWorklist = ref (empty String.compare)
val simplifyWorklist = ref (empty String.compare)
val alias = ref (tabNueva())
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


fun findInTab(x,tab) = case tabBusca(x,tab) of SOME s=>addList(empty String.compare,s) | NONE => raise Fail "Nodo no encontrado"
fun build (FGRAPH {control, def, use, ismove}) nodes outsarray =
	let
		val _ = adjSet := (empty (fn ((u0,v0),(u1,v1)) => if u0=u1 then String.compare(v0,v1) else String.compare(u0,u1)))
		val _ = adjList := (tabNueva ())
		val _ = degree := (tabNueva ())
		val _ = moveList := (tabNueva())
		val _ = worklistMoves := (empty compare)
		val _ = activeMoves := (empty compare)
		val _ = constrainedMoves := (empty compare)
		val _ = coalescedMoves := (empty compare)
		val _ = selectStack := []
		val _ = coalescedNodes := (empty String.compare)
		val _ = alias := (tabNueva())


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

fun adjacent n = let val adjlistn = case tabBusca(n,!adjList) of SOME x => x |NONE => raise Fail "node not found"
  					in difference(adjlistn,addList(!coalescedNodes,!selectStack)) end

fun decrementdegree m = ()

fun simplify () = let val wlist = listItems(!simplifyWorklist)
  						val _ = simplifyWorklist := empty String.compare
  						fun aux [] = ()
						  |aux (n :: rest) = let val _ = selectStack := (n :: !selectStack)
						  							val _ = app (fn m => decrementdegree m) (adjacent n)
												in aux rest end
						in aux wlist end

fun getAlias n = if member(!coalescedNodes,n) then getAlias (case tabBusca(n,!alias) of SOME x=>x|NONE=>raise Fail "nnf") else n

fun addWorklist u =
	if not (listmember u precolored) andalso not (moveRelated u andalso (tabBuscaDefaults (!degree, u, 0) < k)) then
		(freezeWorklist := delete(!freezeWorklist,u);
		simplifyWorklist := delete(!simplifyWorklist,u)) else ()

fun ok(t,r) = let val degreet = case tabBusca(t,!degree) of SOME x=>x|NONE=>raise Fail "Nnf"
					in degreet < k orelse listmember t precolored orelse member(!adjSet,(t,r)) end

fun conservative nodes = let
							fun aux [] x = x
								|aux (n::rest) x = let val degreen = case tabBusca(n,!degree) of SOME x=>x|NONE=>raise Fail "Nnf"
														val x = if degreen<k then x else x+1
														in aux rest x end
							in aux (listItems nodes) 0 < k end
fun combine _ = ()

fun coalesce (FGRAPH {control, def, use, ismove}) = let val wlist = listItems (!worklistMoves)
						val _ = worklistMoves := empty compare
						fun aux [] = ()
							|aux (m :: rest) = let val x = getAlias (List.hd (case tabBusca(m,use) of SOME x=>x|NONE=>raise Fail "node not found"))
													val y = getAlias (List.hd (case tabBusca(m,def) of SOME x=>x|NONE=>raise Fail "node not found"))
													val (u,v) = if listmember y precolored then (y,x) else (x,y)
													val _ = if (u=v) then
																(coalescedMoves:=add(!coalescedMoves,m);addWorklist(u))
															else if listmember v precolored orelse member(!adjSet, (u,v)) then
																(constrainedMoves := add(!constrainedMoves,m);
																addWorklist(u);addWorklist(v))
															else if (listmember u precolored andalso (foldl (fn (t,b) => b andalso (ok(t,u))) true (adjacent v)))
																	orelse (not (listmember u precolored) andalso (conservative(union(adjacent(u),adjacent(v))))) then
																(coalescedMoves := add(!coalescedMoves,m);
																combine(u,v);
																addWorklist(u))
															else
																activeMoves:=add(!activeMoves,m)
												in aux rest end
						in aux wlist end


fun main fgraph nodes = 
	let val (insarray, outsarray) = livenessAnalisis (fgraph, nodes)
		val (a,b) = build fgraph nodes outsarray
		val _ = (moveList := a; worklistMoves := b)
		val (a, b, c) = makeWorklist ()
		val _ = (spillWorklist := a; freezeWorklist :=b; simplifyWorklist:=c)
		fun iterate () = if isEmpty(!simplifyWorklist) andalso isEmpty(!worklistMoves) andalso isEmpty(!freezeWorklist) andalso isEmpty(!spillWorklist) then () else (
            if not (isEmpty(!simplifyWorklist)) then simplify ()
            else if not (isEmpty(!worklistMoves)) then coalesce fgraph
			else ()
			(*; iterate ()*)
          )
		val _ = iterate ()
	in (insarray,outsarray, !adjList) end
