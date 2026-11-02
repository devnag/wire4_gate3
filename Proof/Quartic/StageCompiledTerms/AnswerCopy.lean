import Proof.Quartic.Reconstruct.BatchLoopRun
import Proof.Gates.CounterAsm.Copy

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCompiledTerms

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming (marks marks_length)
open NearCubicGates.Close.CounterAsm NearCubicGates.Close.Recovery.HTParts
open NearQuarticWires.Control NearQuarticWires.Reconstruct.Batch

/-- `lem:print`, paper/paper.tex: copy the
compiler's actual framed Terms, return its source head and clear both
local copy counters before erasing and reusing the same call bank. -/
def answerCopier (p : Program) : WM (cns p.tapeCount) lnr :=
  .seq (frameCopy (cbank _ p.outputTape) (cR 6) (fun bit=>emitPair (cT _) (cR 7) bit))
    (.seq (WM.rewind (cbank _ p.outputTape) (cR 6)) (WM.clear (cR 7)))

/-- `prop:time`, paper/paper.tex: the actual
answer copy and both counter returns are linear in its emitted bytes. -/
def answerCopyCost (bits : List Bool) : ℕ := 100*(frame bits).length+10

/-- `lem:print` and `prop:time`, paper/paper.tex: a compiler reply is copied literally, including its
frame delimiter. No Terms value or answer-length register is supplied. -/
theorem answerCopier_spec (cap : ℕ) (p : Program) (bits : List Bool)
    (a : WState (cns p.tapeCount) lnr)
    (hs : a.st (cbank _ p.outputTape)=frame bits)
    (hh : a.sh (cbank _ p.outputTape)=0)
    (hout : a.sh (cT _)=(a.st (cT _)).length)
    (hz : ∀ i,a.val (cR i)=0) (hcap : 2*(frame bits).length+1≤cap) :
    WExec cap (answerCopier p) a
      (appendT a (cT _) (marks (frame bits))) (answerCopyCost bits) := by
  let src:=cbank p.tapeCount p.outputTape
  let dst:=cT p.tapeCount
  have hsd : src≠dst := cne _ (by dsimp [src,dst,cbank,cT];omega)
  have hr : cR (7 : Fin 8)≠cR 6 := cR.injective.ne (by decide)
  have eCopy:=frameCopy_spec cap hsd hr (emits_pair (cap:=cap))
    (d:=2) (by intro bit;rfl) bits [] [] a
    (by simpa only [List.nil_append,List.append_nil] using hs)
    (by simpa using hh) hout (by rw [hz];omega) (by rw [hz];omega)
  let b:=adv src dst (cR 7) (cR 6) a (marks (frame bits)) (frame bits).length
  change WExec cap _ a b _ at eCopy
  have hb6 : b.val (cR 6)=(frame bits).length := by rw [adv_val_SC,hz,Nat.zero_add]
  have hb7 : b.val (cR 7)=2*(frame bits).length := by rw [adv_val_OP hr,hz,marks_length,Nat.zero_add]
  have eBack:=wrewind_spec cap src (cR 6) (frame bits).length b hb6 (by omega)
  let c:=(b.setv (cR 6) 0).seth src (b.sh src-(frame bits).length)
  have hc7 : c.val (cR 7)=2*(frame bits).length := by
    simp only [c,WState.seth_val,WState.setv_val,Function.update_of_ne hr,hb7]
  have eClear:=wclear_spec cap (cR 7) (2*(frame bits).length) c hc7 (by omega)
  refine (eCopy.seq (eBack.seq eClear)).cast cap ?_ (by unfold answerCopyCost;omega)
  change c.setv (cR 7) 0=appendT a dst (marks (frame bits))
  apply WState.eq
  · funext stream
    by_cases hi : stream=src
    · subst stream
      simp [c,b,adv,appendO,appendT,hsd,hh]
    · by_cases ho : stream=dst
      · subst stream
        simp [c,b,adv,appendO,appendT,hsd.symm]
      · simp [c,b,adv,appendO,appendT,Function.update_of_ne hi,Function.update_of_ne ho]
  · rfl
  · funext reg
    by_cases h6 : reg=cR 6
    · subst reg
      simp [c,b,adv,appendO,appendT,hr.symm,hz]
    · by_cases h7 : reg=cR 7
      · subst reg
        simp [c,b,adv,appendO,appendT,hr,hz]
      · simp [c,b,adv,appendO,appendT,Function.update_of_ne h6,Function.update_of_ne h7]
  · rfl

/-- `lem:print`, paper/paper.tex: compiler
answer acquisition never touches the final output tape. -/
theorem answerCopier_avoids (p : Program) : WM.Avoids (cOUT p.tapeCount) (answerCopier p) := by
  simp [answerCopier,WM.Avoids,frameCopy,pairLoop,cellE,emitPair,emitC,WM.fwdC,WM.rewind,
    WM.clear,cbank,cT,cOUT,Fin.ext_iff]
  all_goals omega

end NearQuarticWires.StageCompiledTerms
