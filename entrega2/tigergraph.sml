type node = tigertemp.temp
type graph = (node * node) Splayset.set

fun nodes graph = []
fun succ node = []
fun pred node = []
fun adj node = []
fun eq (n1, n2) = false

fun newGraph () = Splayset.empty (fn ((n0,n1),(n2,n3)) => let val first = String.compare (n0, n2) in
																	(case first of EQUAL => (String.compare (n1, n3))
																				| other => other )
																	end)
fun newNode graph = ""
exception GraphEdge
fun mk_edge {from=n0, to=n1} = ()
fun rm_edge {from=n0, to=n1} = ()

type 'a Table = (node, 'a) tigertab.Tabla

fun nodename node = "" (*For debugging*)
