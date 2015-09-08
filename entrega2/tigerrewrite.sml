open tigerassem
open tigertab
open tigerframe
open Splayset
fun rewriteprogram framedinstrs spilledNodes : (tigerframe.frame option * tigerassem.instr list) list =
	let fun rewriteframedinstr (NONE,x) = (NONE,x)
			| rewriteframedinstr (SOME frame, instrs) = (SOME frame, rewriteframe frame instrs (ref (tabNueva ())))

		and rewriteframe _ [] _ = []
			|rewriteframe frame (LABEL x::instrs) rtab = (LABEL x) :: (rewriteframe frame instrs rtab)
			|rewriteframe frame (MOVE {assem, dst, src} :: instrs) rtab = 
				let
					val srcspilled = (member(spilledNodes,src))
					val dstspilled = (member(spilledNodes,dst))
					val instr = if not srcspilled andalso not dstspilled then MOVE {assem=assem, dst=dst, src=src} else
						let val assemforsrc = if srcspilled then (myIntToString (getSpilledNodeOffset src rtab frame))^"('s0)" else "'s0"
							val newsrc = if srcspilled then tigerframe.fp else src
							val assemfordst = if dstspilled then (myIntToString (getSpilledNodeOffset dst rtab frame))^"('d0)" else "'d0"
							val newdst = if dstspilled then tigerframe.fp else dst
						in
							(OPER {assem = "MOV "^assemforsrc^", "^assemfordst^"\n",
								src = [newsrc],
								dst = [newdst],
								jump=NONE
							})
						end
				in instr :: (rewriteframe frame instrs rtab) end
			|rewriteframe frame (x::instrs) rtab = x :: rewriteframe frame instrs rtab


		and getSpilledNodeOffset temp rtab frame = case tabBusca(temp, !rtab) of SOME n => n
													|NONE => let val tempoffset = (case allocLocal frame true of InFrame n=>n
																												|_=> raise Fail "allocLocal devolvio inreg??")
																in (rtab:= tabRInserta(temp, tempoffset, !rtab); tempoffset) end
	in
		List.map rewriteframedinstr framedinstrs
	end
