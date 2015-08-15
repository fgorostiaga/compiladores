open Splayset
type noderep = string
type graph = (noderep set * noderep * noderep set) set (*{preds}, noderep, {succs}*)
type node = noderep * graph ref 

val emptystringset = empty String.compare

val nxtnode = ref #"a"
val nodei = ref 0
fun nextnode () = let val ret = Char.toString(!nxtnode)^Int.toString(!nodei)
						val _ = if !nxtnode = #"z" then nxtnode := Char.succ (!nxtnode) else (nxtnode := #"a";nodei:= !nodei+1)
						in ret end

fun getnode noderep grafo = (case peek (grafo, (emptystringset, noderep, emptystringset)) of
												NONE => raise Fail "no existia el nodo"
												|SOME m=>m)

fun nodes graph = foldl (fn ((_,n,_),ns) => ((n, ref graph)::ns)) [] graph
fun succ (n, rgr) = let val grafo = !rgr
						val (_, _, succ) = getnode n grafo
						val theList = List.map (fn n => (n,rgr)) (listItems succ)
						in theList end
fun pred (n, rgr) = let val grafo = !rgr
						val (pred, _, _) = getnode n grafo
						val theList = List.map (fn n => (n,rgr)) (listItems pred)
						in theList end
fun adj (n, rgr) = let val grafo = !rgr
						val (pred, _, succ) = getnode n grafo
						val theList = List.map (fn n => (n,rgr)) (listItems (union (succ, pred)))
						in theList end
fun eq ((n0,rgr0), (n1,rgr1)) = String.compare (n0, n1) = EQUAL andalso rgr0 = rgr1

fun newGraph () = empty (fn ((_,n0,_),(_,n1,_)) => String.compare (n0, n1))

fun newNode graph = (nextnode (), ref graph)
exception GraphEdge
fun mk_edge {from=(n0,rgr0), to=(n1,rgr1)} = let val _ = if rgr0 = rgr1 then () else raise Fail "Grafos distintos"
												val (p,_,s) = getnode n0 (!rgr0)
												val nuevoorigen = (p,n0, add (s, n1))
												val grafo = delete(!rgr0, nuevoorigen)
												val _ = rgr0 := add(grafo,nuevoorigen)
												(*Hasta aca agregamos n1 como sucesor de n0*)
												val (p,_,s) = getnode n1 (!rgr0)
												val nuevodestino = (add(p,n0),n1, s)
												val grafo = delete(!rgr0, nuevodestino)
												val _ = rgr0 := add(grafo,nuevodestino)
												in () end
fun rm_edge {from=(n0,rgr0), to=(n1,rgr1)} = let val _ = if rgr0 = rgr1 then () else raise Fail "Grafos distintos"
												val (p,_,s) = getnode n0 (!rgr0)
												val nuevoorigen = (p,n0, delete (s, n1))
												val grafo = delete(!rgr0, nuevoorigen)
												val _ = rgr0 := add(grafo,nuevoorigen)
												(*Hasta aca eliminamos n1 como sucesor de n0*)
												val (p,_,s) = getnode n1 (!rgr0)
												val nuevodestino = (delete(p,n0),n1, s)
												val grafo = delete(!rgr0, nuevodestino)
												val _ = rgr0 := add(grafo,nuevodestino)
												in () end

type 'a Table = (node, 'a) tigertab.Tabla

fun nodename node = "" (*For debugging*)
