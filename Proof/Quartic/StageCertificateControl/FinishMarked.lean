import Proof.Quartic.StageCertificateControl.MeasuredUnframe

/-!
# Close and return a measured marked copy

Paper: `prop:time`, paper/paper.tex.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming (marks marks_length)
open NearCubicGates.Close

variable {ns nr : ℕ}

/-- `prop:time`, paper/paper.tex: closing a
marked copy uses a temporary copy of its actual byte counter, then
returns the destination head by that exact physical distance. -/
def finishMarkedCopy (dst : Fin (ns+1)) (OP tmp scratch : Fin nr) : WM ns nr :=
  .seq (NearCubicWires.WireExponent3_5.FinalPass.Hash4.wcopyR OP tmp scratch)
    (.seq (emitC dst tmp false) (WM.rewind dst tmp))

/-- `prop:time`, paper/paper.tex: the saved
binary payload becomes an exact framed tape at head zero, while its
original measured byte count is retained and both temporary registers
are restored by charged instructions. -/
theorem finishMarkedCopy_spec (cap : ℕ) (dst : Fin (ns+1)) (OP tmp scratch : Fin nr)
    (hOt : OP≠tmp) (hOs : OP≠scratch) (hts : tmp≠scratch)
    (bits : List Bool) (σ : WState ns nr)
    (hd : σ.st dst=marks bits) (hh : σ.sh dst=2*bits.length)
    (hOP : σ.val OP=2*bits.length) (ht : σ.val tmp=0) (hs : σ.val scratch=0)
    (hcap : 2*bits.length+2≤cap) :
    WExec cap (finishMarkedCopy dst OP tmp scratch) σ
      ((σ.sets dst (frame bits)).seth dst 0) (50*bits.length+30) := by
  have ec := NearCubicWires.WireExponent3_5.FinalPass.Hash4.wcopyR_spec cap
    OP tmp scratch hOt hOs hts σ ht hs (by rw [hOP];omega)
  rw [hOP] at ec
  let a := σ.setv tmp (2*bits.length)
  have ee := emitC_spec cap dst tmp false a
    (by simp [a,hd,hh,marks_length]) (by simp [a];omega)
  let b := ((a.sets dst (a.st dst++[false])).seth dst (a.sh dst+1)).setv tmp (a.val tmp+1)
  have er := wrewind_spec cap dst tmp (2*bits.length+1) b (by simp [b,a])
    (by simp [b,a];omega)
  refine (ec.seq (ee.seq er)).cast cap ?_ ?_
  · apply WState.eq
    · funext i
      by_cases hi : i=dst
      · subst i;simp [b,a,hh]
      · simp [b,a,Function.update_of_ne hi]
    · funext i
      by_cases hi : i=dst
      · subst i;simp [b,a,hd,Codec.frame_eq_marks]
      · simp [b,a,Function.update_of_ne hi]
    · funext i
      by_cases hi : i=tmp
      · subst i;simp [ht]
      · simp [b,a,Function.update_of_ne hi]
    · rfl
  · simp [a]
    omega

end NearQuarticWires.StageCertificateControl
