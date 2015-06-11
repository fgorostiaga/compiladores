structure tigerseman :> tigerseman =
struct

open tigerabs
open tigersres
open tigertrans

type expty = {exp: unit, ty: Tipo}

type venv = (string, EnvEntry) tigertab.Tabla
type tenv = (string, Tipo) tigertab.Tabla

val tab_tipos : (string, Tipo) Tabla = tabInserList(
	tabNueva(),
	[("int", TInt RW), ("string", TString), ("_intro", TInt RO)])

val levelPila: tigertrans.level tigerpila.Pila = tigerpila.nuevaPila1(tigertrans.outermost) 
fun pushLevel l = tigerpila.pushPila levelPila l
fun popLevel() = tigerpila.popPila levelPila 
fun topLevel() = tigerpila.topPila levelPila

val tab_vars : (string, EnvEntry) Tabla = tabInserList(
	tabNueva(),
	[("print", Func{level=topLevel(), label="print",
		formals=[TString], result=TUnit, extern=true}),
	("flush", Func{level=topLevel(), label="flush",
		formals=[], result=TUnit, extern=true}),
	("getchar", Func{level=topLevel(), label="getstr",
		formals=[], result=TString, extern=true}),
	("ord", Func{level=topLevel(), label="ord",
		formals=[TString], result=TInt RW, extern=true}),
	("chr", Func{level=topLevel(), label="chr",
		formals=[TInt RW], result=TString, extern=true}),
	("size", Func{level=topLevel(), label="size",
		formals=[TString], result=TInt RW, extern=true}),
	("substring", Func{level=topLevel(), label="substring",
		formals=[TString, TInt RW, TInt RW], result=TString, extern=true}),
	("concat", Func{level=topLevel(), label="concat",
		formals=[TString, TString], result=TString, extern=true}),
	("not", Func{level=topLevel(), label="not",
		formals=[TInt RW], result=TInt RW, extern=true}),
	("exit", Func{level=topLevel(), label="exit",
		formals=[TInt RW], result=TUnit, extern=true})
	])

fun printtipo TUnit = print "TUNIT**"
	|printtipo (TInt _) = print "TINT**"
	|printtipo TNil = print "TNIL**"
	|printtipo TString = print "TSTRING**"
	|printtipo (TArray _) = print "TARRAY**"
	|printtipo (TRecord _) = print "TRECORD**"
	|printtipo (TTipo _) = print "TTIPO**"
	|printtipo (TFunc _) = print "TFUNC**"
	
fun printlist xs = let fun printl2 [] = "]"
			|printl2 [x] = x^"]"
			|printl2 (x::xs) = x^", "^printl2 xs
		in print ("["^(printl2 xs)^"\n") end

fun inlist (x,[]) = false
	|inlist (x, (y::xs)) = if x=y then true else inlist (x, xs)

fun checkrep [] _ = ()
	|checkrep (x::xs) name = if (inlist (x,xs)) then (raise Fail ("Repeticion de "^name)) else (checkrep xs name)

fun tipoReal (TTipo (s, ref (SOME (t)))) = tipoReal t
	| tipoReal t = t

fun tiposIguales (TRecord _) TNil = true
	| tiposIguales TNil (TRecord _) = true 
	| tiposIguales (TRecord (_, u1)) (TRecord (_, u2 )) = (u1=u2)
	| tiposIguales (TArray (_, u1)) (TArray (_, u2)) = (u1=u2)
	| tiposIguales (TTipo (_, r)) b =
		let
			val a = case !r of
				SOME t => t
				| NONE => raise Fail "No debería pasar! (1)"
		in
			tiposIguales a b
		end
	| tiposIguales a (TTipo (_, r)) =
		let
			val b = case !r of
				SOME t => t
				| NONE => raise Fail "No debería pasar! (2)"
		in
			tiposIguales a b
		end
	| tiposIguales (TInt _) (TInt _) = true
	| tiposIguales a b = (a=b)

fun mockVar ty escap = Var {ty = ty, access = allocLocal (topLevel ()) escap, level=(getActualLev ())}

fun isInt (TInt _) = true
	| isInt _ = false

fun error(s, p) = raise Fail ("Error -- línea "^Int.toString(p)^": "^s^"\n")

fun mychecktipo a b nl = if not (tiposIguales a b) then (error("error de tipos",nl)) else ()

fun transExp(venv, tenv) =

	let
		fun solvety (ty, tenv) = if tabEsta(ty, tenv) then (tabSaca(ty, tenv)) else raise Fail "Error de tipos. Tipo inexistente en la tabla"
		fun trexp(VarExp v) = trvar(v)
		| trexp(UnitExp _) = {exp=unitExp(), ty=TUnit}
		| trexp(NilExp _)= {exp=nilExp(), ty=TNil}
		| trexp(IntExp(i, _)) = {exp=intExp i, ty=TInt RW}
		| trexp(StringExp(s, _)) = {exp=stringExp(s), ty=TString}
		| trexp(CallExp({func=f, args}, nl)) =
			let
				val (TArgs, ext, TRet, lev, lab) =
				case tabBusca (f, venv) of
					SOME (Func {formals, extern, result, level, label}) => (formals, extern, result, level, label)
					|SOME _ => error(f^": no es funcion", nl)
					|NONE => error(f^": no existe", nl)
				fun aux [] [] r = r
					|aux [] _ _ = raise Fail "muchos args"
					|aux _ [] _ = raise Fail "pocos args"
					|aux (t::tt) (a::aa) r =
					let val {exp = ae', ty=at'} = trexp a
						val _ = mychecktipo t at' nl
					in aux tt aa r@[{exp=ae', ty=at'}] end
				val leargs = aux TArgs args []
				val leargs' = map (fn {exp, ty} => exp) leargs
				val pf = TRet = TUnit
			in {exp=callExp (lab, ext, pf, lev, leargs'), ty=TRet} end (*COMPLETAR pponele que ya esta*)
		| trexp(OpExp({left, oper=EqOp, right}, nl)) =
			let
				val {exp=expl, ty=tyl} = trexp left
				val {exp=expr, ty=tyr} = trexp right
			in
				if tiposIguales tyl tyr andalso not (tyl=TNil andalso tyr=TNil) andalso tyl<>TUnit then 
					{exp=if tiposIguales tyl TString then binOpStrExp {left=expl,oper=EqOp,right=expr} else binOpIntRelExp {left=expl,oper=EqOp,right=expr}, ty=TInt RW}
					else error("Tipos no comparables", nl)
			end
		| trexp(OpExp({left, oper=NeqOp, right}, nl)) = 
			let
				val {exp=expl, ty=tyl} = trexp left
				val {exp=expr, ty=tyr} = trexp right
			in
				if tiposIguales tyl tyr andalso not (tyl=TNil andalso tyr=TNil) andalso tyl<>TUnit then 
					{exp=if tiposIguales tyl TString then binOpStrExp {left=expl,oper=NeqOp,right=expr} else binOpIntRelExp {left=expl,oper=NeqOp,right=expr}, ty=TInt RW}
					else error("Tipos no comparables", nl)
			end
		| trexp(OpExp({left, oper, right}, nl)) = 
			let
				val {exp=expl, ty=tyl} = trexp left
				val {exp=expr, ty=tyr} = trexp right
			in
				if tiposIguales tyl tyr then
					case oper of
						PlusOp => if isInt (tipoReal tyl) then {exp=binOpIntExp {left=expl, oper=oper, right=expr},ty=TInt RW} else error("Error de tipos", nl)
						| MinusOp => if isInt (tipoReal tyl) then {exp=binOpIntExp {left=expl, oper=oper, right=expr},ty=TInt RW} else error("Error de tipos", nl)
						| TimesOp => if isInt (tipoReal tyl) then {exp=binOpIntExp {left=expl, oper=oper, right=expr},ty=TInt RW} else error("Error de tipos", nl)
						| DivideOp => if isInt (tipoReal tyl) then {exp=binOpIntExp {left=expl, oper=oper, right=expr},ty=TInt RW} else error("Error de tipos", nl)
						| LtOp => if isInt (tipoReal tyl) orelse tipoReal tyl=TString then
							{exp=if isInt (tipoReal tyl) then binOpIntRelExp {left=expl,oper=oper,right=expr} else binOpStrExp {left=expl,oper=oper,right=expr},ty=TInt RW} 
							else error("Error de tipos", nl)
						| LeOp => if isInt (tipoReal tyl) orelse tipoReal tyl=TString then 
							{exp=if isInt (tipoReal tyl) then binOpIntRelExp {left=expl,oper=oper,right=expr} else binOpStrExp {left=expl,oper=oper,right=expr},ty=TInt RW} 
							else error("Error de tipos", nl)
						| GtOp => if isInt (tipoReal tyl) orelse tipoReal tyl=TString then
							{exp=if isInt (tipoReal tyl) then binOpIntRelExp {left=expl,oper=oper,right=expr} else binOpStrExp {left=expl,oper=oper,right=expr},ty=TInt RW} 
							else error("Error de tipos", nl)
						| GeOp => if isInt (tipoReal tyl) orelse tipoReal tyl=TString then
							{exp=if isInt (tipoReal tyl) then binOpIntRelExp {left=expl,oper=oper,right=expr} else binOpStrExp {left=expl,oper=oper,right=expr},ty=TInt RW} 
							else error("Error de tipos", nl)
						| _ => raise Fail "No debería pasar! (3)"
				else error("Error de tipos", nl)
			end
		| trexp(RecordExp({fields, typ}, nl)) =
			let
				(* Traducir cada expresión de fields *)
				val tfields = map (fn (sy,ex) => (sy, trexp ex)) fields

				(* Buscar el tipo *)
				val (tyr, cs) = case tabBusca(typ, tenv) of
					SOME t => (case tipoReal t of
						TRecord (cs, u) => (TRecord (cs, u), cs)
						| _ => error(typ^" no es de tipo record", nl))
					| NONE => error("Tipo inexistente ("^typ^")", nl)
				
				(* Verificar que cada campo esté en orden y tenga una expresión del tipo que corresponde *)
				fun verificar _ [] [] = []
				| verificar _ (c::cs) [] = error("Faltan campos", nl)
				| verificar _ [] (c::cs) = error("Sobran campos", nl)
				| verificar n ((s,t,_)::cs) ((sy,{exp,ty})::ds) =
						if s<>sy then error("Error de campo", nl)
						else if tiposIguales ty t then (exp, n)::(verificar (n+1) cs ds)
							else error("Error de tipo del campo "^s, nl)
				val lf = verificar 0 cs tfields
			in
				{exp=recordExp lf, ty=tyr}
			end
		| trexp(SeqExp(s, nl)) =
			let
				val lexti = map trexp s
				val exprs = map (fn{exp, ty} => exp) lexti
				val {exp, ty=tipo} = hd(rev lexti)
			in { exp=seqExp (exprs), ty=tipo } end
		| trexp(AssignExp({var=SimpleVar s, exp}, nl)) =
			let
				val {exp = e0, ty=ti} = trvar(SimpleVar s,nl)
				val _ = if (ti=TInt RO) then raise Fail (s^" no asignable") else ()
				val {exp = e1, ty = td} = trexp exp
				val _ = mychecktipo ti td nl
			in {exp=assignExp {var=e0,exp=e1}, ty=TUnit} (*COMPLETAR capaz que ya esta*) end
		| trexp(AssignExp({var, exp}, nl)) =
			let
				val {exp = e0, ty=ti} = trvar (var, nl)
				val {exp = e1, ty=td} = trexp exp
				val _ = mychecktipo ti td nl
			in {exp=assignExp {var=e0,exp=e1}, ty=TUnit} end (*COMPLETAR capaz que ya esta*)
		| trexp(IfExp({test, then', else'=SOME else'}, nl)) =
			let
				val {exp=testexp, ty=tytest} = trexp test
				val {exp=thenexp, ty=tythen} = trexp then'
				val {exp=elseexp, ty=tyelse} = trexp else'
			in
				if isInt (tipoReal tytest) andalso tiposIguales tythen tyelse then
					{exp=if tipoReal tythen=TUnit then ifThenElseExpUnit {test=testexp,then'=thenexp,else'=elseexp} else ifThenElseExp {test=testexp,then'=thenexp,else'=elseexp}, ty=tythen}
				else error("Error de tipos en if" ,nl)
			end
		| trexp(IfExp({test, then', else'=NONE}, nl)) =
			let
				val {exp=exptest,ty=tytest} = trexp test
				val {exp=expthen,ty=tythen} = trexp then'
			in
				if isInt (tipoReal tytest) andalso tythen=TUnit then
					{exp=ifThenExp{test=exptest, then'=expthen}, ty=TUnit}
				else error("Error de tipos en if", nl)
			end
		| trexp(WhileExp({test, body}, nl)) =
			let
				val ttest = trexp test
				val _ = preWhileForExp ()
				val tbody = trexp body
			in
				if isInt (tipoReal (#ty ttest)) andalso #ty tbody = TUnit then let val retval = {exp=whileExp {test=(#exp ttest), body=(#exp tbody), lev=topLevel()}, ty=TUnit}
													val _ = postWhileForExp ()
												in retval end
				else if not (isInt(tipoReal (#ty ttest))) then error("Error de tipo en la condición", nl)
				else error("El cuerpo de un while no puede devolver un valor", nl)
			end
		| trexp(ForExp({var, escape, lo, hi, body}, nl)) =
			let 
				val {exp = elo, ty = tlo} = trexp lo
				val _ = mychecktipo tlo (TInt RW) nl
				val {exp = ehi, ty = thi} = trexp hi
				val _ = mychecktipo thi (TInt RW) nl
				val (nenv, _, expsdec) = let val myDecl = VarDec ({name=var,escape=escape,typ=SOME "_intro",init=lo},nl) in trdec (venv, tenv) myDecl end
				val _ = preWhileForExp ()
				val {exp = ebody, ty = tbody} = transExp(nenv, tenv) body
				val _ = mychecktipo tbody TUnit nl
			in
				let val retval = {exp=forExp {lo=elo, hi=ehi, var=hd expsdec, body=ebody}, ty=TUnit}
					val _ = postWhileForExp ()
				in retval end (*COMPLETAR, capaz que ya esta*)
			end
		| trexp(LetExp({decs, body}, _)) =
			let
				fun aux (d, (v, t, exps1)) =
					let
						val (v', t', exps2) = trdec (v, t) d
					in
						(v', t', exps1@exps2)
					end
				val (venv', tenv', expdecs) = List.foldl aux (venv, tenv, []) decs
				val {exp=expbody,ty=tybody}=transExp (venv', tenv') body
			in 
				{exp=seqExp(expdecs@[expbody]), ty=tybody}
			end
		| trexp(BreakExp nl) =
			{exp=breakExp(), ty=TUnit} (*COMPLETAR capaz que ya esta*)
		| trexp(ArrayExp({typ, size, init}, nl)) =
			let fun gettipoarray (TArray (s,_)) = s
				|gettipoarray _ = error("El tipo no es un arreglo", nl)		
			
				val {exp=esize, ty=tisize} = trexp size
				val {exp=einit, ty=tinit} = trexp init
				val _ = mychecktipo tisize (TInt RW) nl
				val realti = (case tabBusca(typ,tenv) of SOME t => tipoReal t
									|NONE => error("no existe el tipo", nl))
				val _ = mychecktipo (gettipoarray realti) tinit nl
			in
				{exp=arrayExp {size=esize, init=einit}, ty=realti}
			end (*COMPLETAR capaz que ya esta*)
			
		and trvar(SimpleVar s, nl) =
			let
				val (t,acc,l) = (case tabBusca(s, venv) of SOME (Var {ty=t, access=acc, level=l}) => (t,acc,l)
							|SOME (Func _) => error(s^" es una funcion", nl)
							| _ => error(s^": no existe", nl))
			in
				{exp=simpleVar (acc, l), ty=t}
			end (*COMPLETAR (capaz que ya esta) *)
		| trvar(FieldVar(v, s), nl) =
			let
				val {exp=evar, ty=ti} = trvar(v, nl)
				fun fields (TRecord (xs,_)) = xs
					|fields _ = error("No es record", nl)
				(*val _ = printlist (List.map (fn (n,_,_)=>n) (fields (tipoReal ti)))*)
				fun getTypeAndIndex ([],_,n) = error(s^" no es un miembro", nl)
					|getTypeAndIndex (((name, ty, _)::xs), s,n) = if name=s then (ty,n) else getTypeAndIndex (xs,s,n+1)
				val (td,index) = getTypeAndIndex(fields (tipoReal ti), s,0)
			in
				{exp=fieldVar (evar, index), ty=td}
			end (*COMPLETAR, capaz que ya esta. Ponele.*)
		| trvar(SubscriptVar(v, i), nl) =
			let
				val {exp=evar, ty=ti} = trvar(v,nl)
				val {exp = eind, ty=td} = trexp i
				val _ = mychecktipo td (TInt RW) nl
				fun tipo (TArray (t,_)) = t
					|tipo (TRecord _) = error("ES trecord",nl)
					|tipo TUnit = error("es tunit",nl)
					|tipo _ = error("No es un array", nl)
				val typ = tipo (tipoReal ti)
			in
				{exp=subscriptVar (evar, eind), ty=typ}
			end (*COMPLETAR, capaz que ya esta. Ponele.*)
		and trdec (venv, tenv) (VarDec ({name,escape,typ=NONE,init},pos)) = 
			let
				fun gettype(init) = let val {exp=e, ty=ti} = transExp(venv, tenv) init
									in (case ti of TNil => raise Fail "Nil not constrained"
													| t => (t,e)) end
			in let val (ty,ex) = (gettype (init)) in
					(tabRInserta (name, mockVar ty (!escape), venv), tenv, [ex])
				end 
			end (*COMPLETAR, capaz que ya esta, cuando saquemos mockVar*)
		| trdec (venv,tenv) (VarDec ({name,escape,typ=SOME s,init},pos)) =
			let
				fun gettype(s, init) = let val ti = (case tabBusca(s,tenv) of SOME t => tipoReal t
									|NONE => error("no existe el tipo", pos))
								val {exp=e, ty=td} = transExp(venv, tenv) init
								val _ = mychecktipo ti td pos
							in (ti,e) end
			in let val (ty,ex) = (gettype (s, init)) in
					(tabRInserta (name, mockVar ty (!escape), venv), tenv, [ex])
				end 
			end (*COMPLETAR, capaz que ya esta, cuando saquemos mockVar*)
		| trdec (venv,tenv) (FunctionDec fs) =
			let fun solvetipo (NONE) = TUnit
					|solvetipo(SOME t) = (case tabBusca(t,tenv) of SOME t => tipoReal t
											|NONE => raise Fail ("no existe el tipo\n"))
				fun transTy(NameTy s) = solvetipo(SOME s)
					|transTy _ = raise Fail "error en argumentos a funcion"
					
				val _ = checkrep (List.map (fn (a,b)=> #name(a)) fs) "funciones"
				
				fun add ([],env) = env
					|add ((({name=f, params=ps, result=r, body=b}, i)::fs),env) = let val myLabel = tigertemp.newlabel () in add (fs, tabRInserta(f, Func {level=newLevel {parent=topLevel (), name=myLabel, formals = (List.map (fn p => !(#escape p)) ps)}, label= myLabel, formals= (List.map (fn p => transTy(#typ p)) ps), result = solvetipo(r), extern=false}, env)) end
				
				fun checkformals([],_) = ()
					|checkformals ({name= n0, escape= b, typ= ty}::ps,i) = let fun inlist({name= n0, escape= _, typ= _}, []) = false
													|inlist({name= n0, escape= b, typ= t}, ({name= n1, escape= _, typ= _}::xs)) = if n0=n1 then true else inlist({name= n0, escape= b, typ= t}, xs)
												in if inlist({name= n0, escape= b, typ= ty},ps) then error("Repeticion de formal "^n0,i) else checkformals(ps,i) end
				
				fun addformals(env, [],_) = env
					|addformals(env, ({name= n, escape= b, typ= ty}::ps),i) = addformals(tabRInserta(n, mockVar (transTy (ty)) (!b) , env), ps,i)
				
				fun checkf([], env) = ()
					|checkf((({name=f, params=ps, result=r, body=b}, i)::fs),env) = let val _ = checkformals(ps, i)
														val {exp=e, ty=t} = transExp(addformals(env,ps,i), tenv) b
														val _ = mychecktipo (solvetipo(r)) t i
														val _ = let val (funLevel, isproc) = (case tabBusca (f, env) of
																										SOME (Func {formals, extern, result, level, label}) => (level, result = TUnit)
																										| _ => raise Fail "No deberia pasar") in functionDec (e,funLevel, isproc) end
													in () end
				fun addycheck (fs, env) = let val nenv = add(fs, env)
								val _ = checkf(fs,nenv)
							in nenv end
				val _ = preFunctionDec ()
			in 
				let val retval = (addycheck(fs, venv), tenv, [])
					val _ = postFunctionDec ()
				in retval end
			end (*COMPLETAR, capaz que ya esta, cuando saquemos mockVar*)
		| trdec (venv,tenv) (TypeDec ts) =
			let 
				fun adddep (({name=n, ty=NameTy t},_), l) = ((t,n)::l)
					|adddep (({name=n, ty = ArrayTy t},_), l) = ((t,n)::l)
					|adddep (_,l) = l
				fun creargrafo ts = List.foldl adddep [] ts
				fun ordenar g = topsort.topsort g
				val ordenado = ordenar (creargrafo ts)
				(*val _ = printlist ordenado*)

				val _ = checkrep (List.map (fn (a,b) => #name(a)) ts) "tipos"

				fun addtotenvnone((({name = n, ty=NameTy a},_)::ds), tenv) = let val ntenv = addtotenvnone(ds, tenv) in tabRInserta(n, TTipo (a, ref NONE), ntenv) end
					|addtotenvnone((({name = n, ty=ArrayTy a},_)::ds), tenv) = let (*val _ = print (" AGREGANDO "^n)*) val ntenv = addtotenvnone(ds, tenv) in tabRInserta(n, TArray (TTipo (a, ref NONE), ref ()), ntenv) end
					|addtotenvnone((({name = n, ty=RecordTy fds},_)::ds), tenv) = let
														fun uniq [] = []
															|uniq [a] = [a]
															|uniq (h::(x as (i::t))) = if ((#name h)=(#name i)) then raise Fail ("Se repiten nombres en el record\n") else uniq x
														fun sort [] = []
															|sort [x] = [x]
															|sort (x::xs) = let val (x1,x2) = List.partition (fn a => (#name a)<(#name x)) xs
																	in (sort x1 @ (x::sort x2)) end
														fun numerar [] n = []
															|numerar ({name= nombre, escape=br, typ=NameTy s}::fds) n = ((nombre, TTipo(s, ref NONE), n)::(numerar fds (n+1)))
															|numerar _ _ = raise Fail "Numerar sobre no NameTy!!"
														val ntenv = addtotenvnone(ds, tenv)
														val lista = sort fds
														val _ = uniq lista
													in tabRInserta(n, TRecord (numerar fds 0, ref ()), ntenv) end
					|addtotenvnone([],tenv)=tenv
				
				
				fun addtotenv((({name = n, ty=t},_)::ds), tenv) = let val ntenv = addtotenv(ds, tenv)
											(*val _ = print (" Actualiza "^n)*)
											val _ = if tabEsta(n,ntenv) then (case tabSaca (n,ntenv) of TTipo (a,b)=> b:=SOME (solvety(a,ntenv))
																		|TArray (TTipo (a,b),_) => b:=SOME (solvety(a,ntenv))
																		|TRecord (fds, _) => (List.map (fn (_,x,_) => (case x of TTipo (a,b) =>b:=SOME (solvety(a,ntenv))
																									|_ => raise Fail "No aplicado sobre TTipo!!")) fds;())
																		| _ => raise Fail "nada") else raise Fail (n^" no existe")
										in ntenv end
					|addtotenv([],tenv)=tenv

			in
				(venv, addtotenv(ts, addtotenvnone(ts,tenv)), []) end (*COMPLETAR*)
		in trexp end
	fun transProg ex =
		let	val main =
					LetExp({decs=[FunctionDec[({name="_tigermain", params=[],
									result=SOME "int", body=SeqExp([ex, IntExp(0,0)],0)}, 0)]],
							body=UnitExp 0}, 0)
			val {exp = e, ty = tbody} = transExp(tab_vars, tab_tipos) main
			val _ = print (Ir (getResult ()))
		in	print "bien!\n" end
	end
