import Proof.Quartic.StageGamma.Retain
import Proof.Quartic.Reconstruct.BatchLoop

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyCollector

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming (marks marks_length)
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Codec
open NearCubicGates.Close.Recovery.HTParts
open NearQuarticWires.Reconstruct.Batch (appendT)

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: the retained
finite context is copied into a request and its source head is returned
before reading the next actual compiled entry. -/
def copyContext (src dst : Fin (ns+1)) (K : Fin nr) : WM ns nr :=
  .seq (.whs src (copyPairW src dst K)) (WM.rewind src K)

/-- `lem:print` and `prop:time`, paper/paper.tex: repeated context copying preserves every register and
source byte, pays the return of the source head and writes no delimiter. -/
theorem copyContext_spec (cap : ℕ) (src dst : Fin (ns+1)) (K : Fin nr)
    (hsd : src≠dst) (bits rest : List Bool) (a : WState ns nr)
    (hs : a.st src=frame bits++rest) (hh : a.sh src=0)
    (hd : a.sh dst=(a.st dst).length) (hz : a.val K=0)
    (hc : 2*bits.length≤cap) :
    WExec cap (copyContext src dst K) a
      (appendT a dst (Streaming.marks bits)) (40*bits.length+5) := by
  have eCopy:=copyFrame_loop cap src dst hsd K rest bits [] a
    (by simpa only [List.nil_append] using hs) (by simpa using hh) hd (by rw [hz];omega)
  simp only [List.length_nil,Nat.zero_add] at eCopy
  let b:=(appendO a dst K (Streaming.marks bits)).seth src (2*bits.length)
  have hb : b.val K=2*bits.length := by simp [b,appendO,hz,Streaming.marks_length]
  have eBack:=wrewind_spec cap src K (2*bits.length) b hb (by rw [hb];exact hc)
  have he : WExec cap (copyContext src dst K) a
      ((b.setv K 0).seth src (b.sh src-2*bits.length))
      ((22*bits.length+1)+1+(5*(2*bits.length)+1)) := WExec.seq eCopy eBack
  refine he.cast cap ?_ (by omega)
  apply WState.eq
  · funext i
    by_cases hi : i=src
    · subst i
      simp [b,appendO,appendT,hsd,hh]
    · by_cases ho : i=dst
      · subst i
        simp [b,appendO,appendT,hsd.symm]
      · simp [b,appendO,appendT,Function.update_of_ne hi,Function.update_of_ne ho]
  · rfl
  · funext j
    by_cases hj : j=K
    · subst j
      simp [b,appendO,appendT,hz]
    · simp [b,appendO,appendT,Function.update_of_ne hj]
  · rfl

end NearQuarticWires.StageGreedyCollector
