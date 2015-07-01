structure tigertrans :> tigertrans = struct

open tigerframe
open tigertree
open tigertemp
open tigerabs
open tigercanon
open Listsort
(*load "Listsort"*)

exception breakexc
exception divCero
	
type level = {parent:frame option , frame: frame, level: int}
type access = tigerframe.access

type frag = tigerframe.frag

val actualLevel = ref ~1 (* _tigermain debe tener level = 0. *)
fun getActualLev() = !actualLevel

val outermost: level = {parent=NONE,
	frame=newFrame{name="_tigermain", formals=[]}, level=getActualLev()}
fun newLevel{parent={parent, frame, level}, name, formals} =
	{
	parent=SOME frame,
	frame=newFrame{name=name, formals=formals},
	level=level+1}
fun allocArg{parent, frame, level} b = tigerframe.allocArg frame b
fun allocLocal{parent, frame, level} b = tigerframe.allocLocal frame b
fun formals{parent, frame, level} = tigerframe.formals frame

datatype exp =
	Ex of tigertree.exp
	| Nx of tigertree.stm
	| Cx of label * label -> tigertree.stm

fun seq [] = EXP (CONST 0)
	| seq [s] = s
	| seq (x::xs) = SEQ (x, seq xs)

fun unEx (Ex e) = e
	| unEx (Nx s) = ESEQ(s, CONST 0)
	| unEx (Cx cf) =
	let
		val r = newtemp()
		val t = newlabel()
		val f = newlabel()
	in
		ESEQ(seq [MOVE(TEMP r, CONST 1),
			cf (t, f),
			LABEL f,
			MOVE(TEMP r, CONST 0),
			LABEL t],
			TEMP r)
	end

fun unNx (Ex e) = EXP e
	| unNx (Nx s) = s
	| unNx (Cx cf) =
	let
		val t = newlabel()
		val f = newlabel()
	in
		seq [cf(t,f),
			LABEL t,
			LABEL f]
	end

fun unCx (Nx s) = raise Fail ("Error (UnCx(Nx..))")
	| unCx (Cx cf) = cf
	| unCx (Ex (CONST 0)) =
	(fn (t,f) => JUMP(NAME f, [f]))
	| unCx (Ex (CONST _)) =
	(fn (t,f) => JUMP(NAME t, [t]))
	| unCx (Ex e) =
	(fn (t,f) => CJUMP(NE, e, CONST 0, t, f))

fun canonizeFrag (PROC{body, frame}) = List.map (fn stm=> PROC {body=stm, frame=frame}) (traceSchedule (basicBlocks(linearize body)))
	| canonizeFrag x = [x]

fun otroCanonizeFrag xs =
	let fun router xs ys [] = (xs,ys)
			|router xs ys (PROC x :: mas) = canonizeFragProc xs ys (PROC x :: mas)
			|router xs ys (STRING (a,b) :: mas) = router xs ((a,b) :: ys) mas
		and canonizeFragProc xs ys (PROC {body, frame} :: mas) = router (((traceSchedule (basicBlocks (linearize body))),frame)::xs) ys mas
			|canonizeFragProc _ _ _ = raise Fail "No deberia pasar"
	in router [] [] xs
	end
(*Grande Felii*)

fun Ir(e) =
	let	fun aux(Ex e) = tigerit.tree(EXP e)
		| aux(Nx s) = tigerit.tree(s)
		| aux _ = raise Fail "bueno, a completar!"
		fun aux2(PROC{body, frame}) = aux(Nx body)
		| aux2(STRING(l, "")) = l^":\n"
		| aux2(STRING("", s)) = "\t"^s^"\n"
		| aux2(STRING(l, s)) = l^":\t"^s^"\n"
		fun aux3 [] = ""
		| aux3(h::t) = (aux2 h)^(aux3 t)
	in	aux3 e end
fun nombreFrame frame = print(".globl " ^ tigerframe.name frame ^ "\n")

(* While y for necesitan la u'ltima etiqueta para un break *)
local
	val salidas: label option tigerpila.Pila = tigerpila.nuevaPila1 NONE
in
	val pushSalida = tigerpila.pushPila salidas
	fun popSalida() = tigerpila.popPila salidas
	fun topSalida() =
		case tigerpila.topPila salidas of
		SOME l => l
		| NONE => raise Fail "break incorrecto!"			
end

val datosGlobs = ref ([]: frag list)
fun procEntryExit{level: level, body} =
	let	val label = STRING(name(#frame level), "")
		val body' = PROC{frame= #frame level, body=unNx body}
		val final = STRING(";;-------", "")
		val _ = print ("ADDED "^ (name (#frame level))^"\n")
	in	datosGlobs:=(!datosGlobs@[label, body', final]) end
fun getResult() = !datosGlobs

fun stringLen s =
	let	fun aux[] = 0
		| aux(#"\\":: #"x"::_::_::t) = 1+aux(t)
		| aux(_::t) = 1+aux(t)
	in	aux(explode s) end

fun stringExp(s: string) =
	let	val l = newlabel()
		val len = ".long "^makestring(stringLen s)
		val str = ".string \""^s^"\""
		val _ = datosGlobs:=(!datosGlobs @ [STRING(l, len), STRING("", str)])
	in	Ex(NAME l) end
fun preFunctionDec() =
	(pushSalida(NONE);
	actualLevel := !actualLevel+1)
fun functionDec(e, l, proc) =
	let	val body =
				if proc then unNx e
				else MOVE(TEMP rv, unEx e)
		val body' = procEntryExit1(#frame l, body)
		val () = procEntryExit{body=Nx body', level=l}
	in	Ex(CONST 0) end
fun postFunctionDec() =
	(popSalida(); actualLevel := !actualLevel-1)

fun unitExp() = Ex (CONST 0)

fun nilExp() = Ex (CONST 0)

fun intExp i = Ex (CONST i)

fun jumper 0 = TEMP fp
	|jumper n = MEM (jumper (n-1)) (*home made*)

fun simpleVar(acc, nivel) =
	let
		fun myexp (InReg l) _ = TEMP l
			|myexp (InFrame k) n = MEM(BINOP(PLUS, jumper n, CONST k))
		val levDif = getActualLev () - nivel
	in
		Ex (myexp acc levDif) (*COMPLETAR, quiza ya este*)
	end

fun varDec(acc) = simpleVar(acc, getActualLev())

fun fieldVar(var, fieldindex) = 
	let val varEx = unEx var in
		Ex (BINOP (PLUS, varEx,
					BINOP(MUL, CONST fieldindex, CONST tigerframe.wSz)))
	end (*COMPLETAR capaz que ya esta*)

fun subscriptVar(arr, ind) =
let
	val a = unEx arr
	val i = unEx ind
	val ra = newtemp()
	val ri = newtemp()
in
	Ex( ESEQ(seq[MOVE(TEMP ra, a),
		MOVE(TEMP ri, i),
		EXP(externalCall("_checkindex", [TEMP ra, TEMP ri]))],
		MEM(BINOP(PLUS, TEMP ra,
			BINOP(MUL, TEMP ri, CONST tigerframe.wSz)))))
end

fun recordExp ls =
	let
		val cuantos = CONST (length ls)
	(*	fun sort [] = []
                   |sort [x] = [x]
                   |sort (x::xs) = let val (x1,x2) = List.partition (fn a => (#name a)<(#name x)) xs
                   in (sort x1 @ (x::sort x2)) end
                val ls_s = sort ls
		val ls_ordenada = Listsort.sort (fn ((_,m),(_,n)) => Int.compare (m,n)) ls *)
		(*lo que intento hacer es ordenar los argumentos del record para que se pueda declarar una variable con los argumentos intercambiados llamados por sus nombres, ver barufatest.sig *)
		val exps = map (fn (exp, _) => unEx exp) ls
	in
	Ex (externalCall("_allocRecord", cuantos::exps))
end (* COMPLETAR capaz que ya esta*)

fun arrayExp{size, init} =
let
	val s = unEx size
	val i = unEx init
in
	Ex (externalCall("_initArray", [s, i]))
end

fun callExp (name,external,isproc,lev:level,ls) = 
	let val ex = if external then (externalCall (name, map (fn x => unEx x) ls)) else
		let val jump = getActualLev () - #level lev + 1
		in
			(CALL (NAME name, (jumper jump) :: map (fn x => unEx x) ls))
		end
	in (*if isproc then Nx ex else*) Ex ex end (*COMPLETAR, capaz que ya esta*)

fun letExp ([], body) = Ex (unEx body)
 |  letExp (inits, body) = Ex (ESEQ(seq inits,unEx body))

fun breakExp() = let
			val l = topSalida ()
		in
	Nx (JUMP (NAME l, [l])) (*COMPLETAR, capaz que ya esta*) end

fun seqExp ([]:exp list) = Nx (EXP(CONST 0))
	| seqExp (exps:exp list) =
		let
			fun unx [e] = []
				| unx (s::ss) = (unNx s)::(unx ss)
				| unx[] = []
		in
			case List.last exps of
				Nx s =>
					let val unexps = map unNx exps
					in Nx (seq unexps) end
				| Ex e => Ex (ESEQ(seq(unx exps), e))
				| cond => Ex (ESEQ(seq(unx exps), unEx cond))
		end

fun preWhileForExp() = pushSalida(SOME(newlabel()))

fun postWhileForExp() = (popSalida(); ())

fun whileExp {test: exp, body: exp, lev:level} =
let
	val cf = unCx test
	val expb = unNx body
	val (l1, l2, l3) = (newlabel(), newlabel(), topSalida())
in
	Nx (seq[LABEL l1,
		cf(l2,l3),
		LABEL l2,
		expb,
		JUMP(NAME l1, [l1]),
		LABEL l3])
end

fun forExp {lo, hi, var, body} =
let
	val explo = unEx lo
	val exphi = unEx hi
	val expvar = unNx var
	val expb = unNx body
	val (l0,l1,l2) = (newlabel(), newlabel(), topSalida())
in
	Nx (seq[expvar,
			LABEL l0,
			CJUMP (EQ, explo, exphi, l1, l2),
			LABEL l1,
			expb,
			JUMP(NAME l0, [l0]),
			LABEL l2])
end (*COMPLETAR, quizas ya este*)

fun ifThenExp{test, then'} =
	let
		val cf = unCx test
		val expthen = unNx then'
		val (l0,l1) = (newlabel(), newlabel())
	in
		Nx (seq[cf(l0,l1),
			LABEL l0,
			expthen,
			LABEL l1])
	end (*COMPLETAR capaz que ya esta*)

fun ifThenElseExp {test,then',else'} =
	let
		val cf = unCx test
		val expthen = unEx then'
		val expelse = unEx else'
		val (l0,l1,l2) = (newlabel(), newlabel(), newlabel())
		val r = newtemp ()
	in
		Ex (ESEQ(seq[cf(l0,l1),
			LABEL l0,
			MOVE(TEMP r, expthen),
			JUMP (NAME l2, [l2]),
			LABEL l1,
			MOVE(TEMP r, expelse),
			LABEL l2],
			TEMP r))
	end (*COMPLETAR capaz que ya esta*)

fun ifThenElseExpUnit {test,then',else'} =
	let
		val cf = unCx test
		val expthen = unNx then'
		val expelse = unNx else'
		val (l0,l1,l2) = (newlabel(), newlabel(), newlabel())
	in
		Nx (seq[cf(l0,l1),
			LABEL l0,
			expthen,
			JUMP (NAME l2, [l2]),
			LABEL l1,
			expelse,
			LABEL l2
			])
	end (*COMPLETAR capaz que ya esta*)

fun assignExp{var, exp} =
let
	val v = unEx var
	val vl = unEx exp
in
	Nx (MOVE(v,vl))
end

fun binOpIntExp {left, oper, right} = 
	let
		val leftexp = unEx left
		val rightexp = unEx right
	in
		case oper of
			PlusOp => Ex (BINOP (PLUS,leftexp,rightexp))
			| MinusOp => Ex (BINOP (MINUS,leftexp,rightexp))
			| TimesOp => Ex (BINOP (MUL,leftexp,rightexp))
			| DivideOp => Ex (BINOP (DIV,leftexp,rightexp))
			|_ => raise Fail ("Error binopintexp")
	end (*COMPLETAR capaz que ya esta*)

fun binOpIntRelExp {left,oper,right} =
	let
		val leftexp = unEx left
		val rightexp = unEx right
	in
		case oper of
			EqOp => Cx (fn (t,f) => CJUMP (EQ, leftexp, rightexp, t, f))
			| NeqOp => Cx (fn (t,f) => CJUMP (NE, leftexp, rightexp, t, f))
			| LtOp => Cx (fn (t,f) => CJUMP (LT, leftexp, rightexp, t, f))
			| LeOp => Cx (fn (t,f) => CJUMP (LE, leftexp, rightexp, t, f))
			| GtOp => Cx (fn (t,f) => CJUMP (GT, leftexp, rightexp, t, f))
			| GeOp => Cx (fn (t,f) => CJUMP (GE, leftexp, rightexp, t, f))
			|_ => raise Fail ("Error binopintrelexp")
	end
	(*COMPLETAR, capaz que ya esta*)

fun binOpStrExp {left,oper,right} =
	let
		val leftexp = unEx left
		val rightexp = unEx right
		val res = Ex (externalCall("_stringCompare", [leftexp, rightexp]))
	in
		binOpIntRelExp {left=res, oper=oper, right=Ex (CONST 0)}
	end (*COMPLETAR capaz ya esta*)

fun ppEXP (Ex e) = "EX (" ^ (tigertree.ppEXP e) ^ ")"
	| ppEXP (Nx s) = "NX (" ^ (tigertree.ppSTM s) ^ ")"
	| ppEXP (Cx f) = "CX algo"

end
