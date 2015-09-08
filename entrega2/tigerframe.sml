(*
	Frames para el 80386 (sin displays ni registers).

		|    argn    |	fp+4*(n+1)
		|    ...     |
		|    arg2    |	fp+16
		|    arg1    |	fp+12
		|	fp level |  fp+8
		|  retorno   |	fp+4
		|   fp ant   |	fp
		--------------	fp
		|   local1   |	fp-4
		|   local2   |	fp-8
		|    ...     |
		|   localn   |	fp-4*n
*)

structure tigerframe :> tigerframe = struct

open tigertree

type level = int

val fp = "%rbp"				(* frame pointer *)
val sp = "SP"				(* stack pointer *)
val rv = "%rax"				(* return value  *)
val ov = "OV"				(* overflow value (edx en el 386) *)
val wSz = 8					(* word size in bytes *)
val log2WSz = 3				(* base two logarithm of word size in bytes *)
val fpPrev = 0				(* offset (bytes) *)
val fpPrevLev = 8			(* offset (bytes) *)
val argsInicial = 0			(* words *)
val argsOffInicial = ~1		(* words *)
val argsGap = wSz			(* bytes *)
val regInicial = 1			(* reg *)
val localsInicial = 0		(* words *)
val localsGap = 0 			(* bytes *)
val calldefs = [rv]
val specialregs = [fp]
val argregs = ["%rdi","%rsi", "%rdx", "%rcx", "%r8", "%r9"] (*Feli was here*)
val callersaves = [rv, "%r10", "%r11"]@argregs
val calleesaves = ["%rbx", "%r12", "%r13", "%r14", "%r15"]

type frame = {
	name: string,
	formals: bool list,
	locals: bool list,
	actualArg: int ref,
	actualLocal: int ref,
	actualReg: int ref
}
type register = string
datatype access = InFrame of int | InReg of tigertemp.label
datatype frag = PROC of {body: tigertree.stm, frame: frame}
	| STRING of tigertemp.label * string
fun newFrame{name, formals} = {
	name=name,
	formals=formals,
	locals=[],
	actualArg=ref argsInicial,
	actualLocal=ref localsInicial,
	actualReg=ref regInicial
}
fun name(f: frame) = #name f
fun string(l, s) = l^tigertemp.makeString(s)^"\n"
val argregslength = List.length(argregs)
fun getArgForPos n = if (n<argregslength) then
						InReg (List.nth(argregs,n)) else
						InFrame ((n-argregslength)*wSz+argsGap)

fun formals({formals=f, ...}: frame) = 
	List.tabulate (List.length(f)+1, getArgForPos) (*+1 por el FP*)

fun formals_ORI({formals=f, ...}: frame) = 
	let	fun aux(n, []) = []
		| aux(n, h::t) = InFrame(n)::aux(n+argsGap, t)
	in aux(argsInicial, (true :: f)) end


fun maxRegFrame(f: frame) = !(#actualReg f)
fun allocArg (f: frame) b = 
	case b of
	true =>
		let	val ret = (!(#actualArg f)+argsOffInicial)*wSz
			val _ = #actualArg f := !(#actualArg f)-1
		in	InFrame ret end
	| false => InReg(tigertemp.newtemp())
fun allocLocal (f: frame) b = 
	case b of
	true =>
		let	val ret = InFrame(((!(#actualLocal f))+(!(#actualArg f))+argsOffInicial)*wSz)
		in	#actualLocal f:=(!(#actualLocal f)-1); ret end
	| false => InReg(tigertemp.newtemp())
fun exp(InFrame k) = MEM(BINOP(PLUS, TEMP(fp), CONST k)) (*Deberia usar el e?*)
| exp(InReg l) = TEMP l
fun externalCall(s, l) = CALL(NAME s, l)

fun procEntryExit1 (frame,body) = body

fun procEntryExit2 (frame,body) = body @ [tigerassem.OPER {assem = "heres a node too\n",
															src = calleesaves,
															dst = [],
															jump = NONE }]

fun myIntToString n = if n<0 then ("-"^(myIntToString (~n))) else (Int.toString n)
fun procEntryExit3 ({name, actualLocal,...}:frame, body) =
	{prolog = "PROCEDURE "^name^" \n"^"pushq %rbp\nsubq $"^(myIntToString wSz)^", %rsp\nmovq %rsp, %rbp\n"
		^"subq $"^(myIntToString (~(!actualLocal)*wSz))^", %rsp\n",
	body = body,
	epilog = "END "^name^"\n"^"addq $8, %rbp\nleave\nret"}

end
