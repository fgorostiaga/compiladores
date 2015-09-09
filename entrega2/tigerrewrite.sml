open tigerassem
open tigertab
open tigerframe
open Splayset

val emptyset = empty String.compare

fun rewriteprogram framedinstrs spilledNodes : (tigerframe.frame option * tigerassem.instr list) list =
	let fun rewriteframedinstr (NONE,x) = (NONE,x)
			| rewriteframedinstr (SOME frame, instrs) = (SOME frame, rewriteframe frame instrs (ref (tabNueva ())))

		and rewriteframe _ [] _ = []
			|rewriteframe frame (LABEL x::instrs) rtab = (LABEL x) :: (rewriteframe frame instrs rtab)
			|rewriteframe frame (MOVE {assem, dst, src} :: instrs) rtab = 
				let
					val srcspilled = (member(spilledNodes,src))
					val dstspilled = (member(spilledNodes,dst))
					val manyinstrs = if not srcspilled andalso not dstspilled then [MOVE {assem=assem, dst=dst, src=src}] else
						if srcspilled andalso dstspilled then
							let val pushinstr = (OPER {assem = "push %rax\n", src=[], dst=[], jump=NONE})
								val firstmovinstr = (OPER {assem = "mov "^(myIntToString (getSpilledNodeOffset src rtab frame))^"(%rbp), %rax\n", src=[], dst=[], jump=NONE})
								val sndmovinstr = (OPER {assem = "mov %rax, "^(myIntToString (getSpilledNodeOffset dst rtab frame))^"(%rbp)\n", src=[], dst=[], jump=NONE})
								val popinstr = (OPER {assem = "pop %rax\n", src=[], dst=[], jump=NONE})
							in
								[pushinstr, firstmovinstr, sndmovinstr, popinstr]
							end
						else
							let val assemforsrc = if srcspilled then (myIntToString (getSpilledNodeOffset src rtab frame))^"('s0)" else "'s0"
								val newsrc = if srcspilled then tigerframe.fp else src
								val assemfordst = if dstspilled then (myIntToString (getSpilledNodeOffset dst rtab frame))^"('d0)" else "'d0"
								val newdst = if dstspilled then tigerframe.fp else dst
							in
								[(OPER {assem = "MOV "^assemforsrc^", "^assemfordst^"\n",
									src = [newsrc],
									dst = [newdst],
									jump=NONE
								})]
							end
				in manyinstrs @ (rewriteframe frame instrs rtab) end
			|rewriteframe frame (OPER {assem, src, dst, jump}::instrs) rtab =
				let
					val localspillednodes = intersection(addList(emptyset,src@dst), spilledNodes)
					val temps2offsetaliastab = foldl (fn (node,tab) => tabRInserta (node, {alias=tigertemp.newtemp (), offset = getSpilledNodeOffset node rtab frame}, tab))  (tabNueva ()) localspillednodes
					fun makepremoves [] = []
						|makepremoves (node :: rest) = let val {alias, offset} = (case tabBusca(node,temps2offsetaliastab) of SOME x=> x | NONE => raise Fail "no encontrado en makepremoves")
															in OPER {assem = "MOV "^myIntToString offset^"('s0), 'd0\n",
																		src = [fp], dst = [alias], jump=NONE} :: makepremoves rest end
					fun makepostmoves [] = []
						|makepostmoves (node :: rest) = let val {alias, offset} = (case tabBusca(node,temps2offsetaliastab) of SOME x=> x | NONE => raise Fail "no encontrado en makepostmoves")
															in OPER {assem = "MOV 's0, "^myIntToString offset^"('d0)\n",
																		src=[alias], dst=[fp], jump=NONE} :: makepostmoves rest end
					val preopers = makepremoves (List.filter (fn node => member(localspillednodes, node)) src)
					val postopers = makepostmoves (List.filter (fn node => member(localspillednodes, node)) dst)
					val newsrc = List.map (fn node => case tabBusca(node, temps2offsetaliastab) of SOME x=> #alias x | NONE => node) src
					val newdst = List.map (fn node => case tabBusca(node, temps2offsetaliastab) of SOME x=> #alias x | NONE => node) dst
				in preopers @ (OPER {assem=assem, src=newsrc, dst= newdst, jump=jump} :: postopers) @ (rewriteframe frame instrs rtab) end




		and getSpilledNodeOffset temp rtab frame = case tabBusca(temp, !rtab) of SOME n => n
													|NONE => let val tempoffset = (case allocLocal frame true of InFrame n=>n
																												|_=> raise Fail "allocLocal devolvio inreg??")
																in (rtab:= tabRInserta(temp, tempoffset, !rtab); tempoffset) end
	in
		List.map rewriteframedinstr framedinstrs
	end
