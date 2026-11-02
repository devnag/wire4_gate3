import Proof.Quartic.StageTupleTermPrice.Steps
import Proof.Quartic.StageTupleTermPrice.Codecs
import Proof.Quartic.StageTupleTermPrice.Weighted

set_option autoImplicit false

namespace NearQuarticWires.StageTupleTermPrice

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Interfaces
open NearCubicWires.WireExponent3_5.CompilerMachine (Top.loadRec)
open StageTuple StageNativeKids

/-- `prop:time`, paper/paper.tex: the
actual one-atom request copies only original source/context bytes,
its finite atom codec and the actual target-width codec. -/
theorem Step.native_word_bound (j : Step) : j.nativeRequest.word.length≤50*j.small := by
  rcases j.monomial.small_bounds with ⟨hpos,hn,hL,hN,hD,hV,hmc,hcall,hheader,hctx⟩
  have hi : j.atom.val≤j.monomial.small:=j.atom.isLt.le.trans hV
  have ha:=natural_word_length j.atom.val
  have hw:=natural_word_length j.monomial.width
  change (Top.loadRec (frame (callWord j.monomial.request.header.call))
    (frame ((StagePrint.Header.baseHeaderValues j.monomial.request.header).flatMap natWord))
    j.monomial.request.contextWord (natWord j.atom.val) (natWord j.monomial.width)
    [] [] [] [] [] []).length≤50*j.monomial.small
  simp only [Top.loadRec,List.length_append,frame_length,List.length_nil]
  nlinarith only [hcall,hheader,hctx,hi,ha,hw,hL,hpos]

/-- `prop:time`, paper/paper.tex: the
fixed actual native-source budget is used unconditionally; no native
price, decoded source or alternative clock is supplied to this theorem. -/
theorem price_nativeBudget : Price Step.small (fun j=>NativeKidsRequest.budget j.nativeRequest) := by
  obtain ⟨C,E,_hC,_hE,h⟩:=StageNativeKids.nativeStagePrice
  refine ⟨C*60^E,E,fun j=>?_⟩
  have hw:=j.native_word_bound
  have hn:=j.monomial.small_bounds.2.1
  have hl:=j.monomial.small_bounds.2.2.1
  change j.monomial.request.header.call.n≤j.small at hn
  change j.monomial.width≤j.small at hl
  have hs:=j.small_pos
  have hh : j.nativeRequest.word.length+j.nativeRequest.header.call.n+j.nativeRequest.outputWidth+1≤60*j.small := by
    change j.nativeRequest.word.length+j.monomial.request.header.call.n+j.monomial.width+1≤_
    omega
  calc
    _≤C*(j.nativeRequest.word.length+j.nativeRequest.header.call.n+j.nativeRequest.outputWidth+1)^E := h j.nativeRequest
    _≤C*(60*j.small)^E := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hh _)
    _=_ := by rw [mul_pow];ring

end NearQuarticWires.StageTupleTermPrice
