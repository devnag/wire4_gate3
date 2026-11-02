import Proof.Quartic.StageCertificateControl.FramePayload
import Proof.Quartic.StageCertificateControl.FinishMarked

/-!
# Copy the preparation suffix into an actual call bank

Paper: Step 2 of `sec:algorithm`, paper/paper.tex,
and `prop:time`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming (marks marks_length)
open NearCubicGates.Close NearCubicGates.Close.WordPrograms

variable {ns nr : ℕ}

/-- `sec:algorithm` and `prop:time`, paper/paper.tex: the literal preparation suffix is copied,
its original source offset is restored by actual counters, and its
call-bank frame is closed and returned to head zero. -/
def copyPreparation (src dst : Fin (ns+1)) (R : Fin 4 ↪ Fin nr) : WMX ns nr :=
  .seq (copyPayload src dst (R 0) (R 1))
    (.seq (WMX.bwd src) (.seq (.wm (WM.rewind src (R 1)))
      (.wm (finishMarkedCopy dst (R 0) (R 2) (R 3)))))

/-- `prop:time`, paper/paper.tex: a real
copy beginning after the index restores that same offset, rather than
rewinding the original source past its index. Its exact marked-byte
count remains available, while all temporary counters are restored. -/
theorem copyPreparation_spec (cap : ℕ) (src dst : Fin (ns+1)) (hsd : src≠dst)
    (R : Fin 4 ↪ Fin nr) (prep : List Bool) (σ : WState ns nr)
    (hread : ∀ q,readTapeBit (σ.st src) (σ.sh src+q)=readTapeBit (frame prep) q)
    (hd : σ.st dst=[]) (hh : σ.sh dst=0) (hz : ∀ i,σ.val (R i)=0)
    (hcap : 4*prep.length+4≤cap) :
    WXExec cap (copyPreparation src dst R) σ
      (((σ.sets dst (frame prep)).seth dst 0).setv (R 0) (2*prep.length))
      (200*prep.length+100) := by
  have rn {i j : Fin 4} (h : i≠j) : R i≠R j := R.injective.ne h
  have ec := copyPayload_exec cap σ src dst (R 0) (R 1) hsd (rn (by decide)) prep []
    (by intro q;simpa only [List.append_nil] using hread q)
    (by rw [hd,hh];rfl) (by rw [hz];omega) (by rw [hz];omega)
  let a := (Control.copySt σ src dst (R 0) (R 1) prep.length (marks prep)).seth src
    (σ.sh src+2*prep.length+1)
  have eb := WXExec.bwd cap src a
  let b := a.seth src (a.sh src-1)
  have er := wrewind_spec cap src (R 1) (2*prep.length) b
    (by simp [b,a,Control.copySt,hz]) (by simp [b,a,Control.copySt,hz];omega)
  let c := (b.setv (R 1) 0).seth src (b.sh src-2*prep.length)
  have ef := finishMarkedCopy_spec cap dst (R 0) (R 2) (R 3)
    (rn (by decide)) (rn (by decide)) (rn (by decide)) prep c
    (by simp [c,b,a,Control.copySt,hd])
    (by simp [c,b,a,Control.copySt,hsd.symm,hh,marks_length])
    (by simp [c,b,a,Control.copySt,rn (show (0 : Fin 4)≠1 by decide),hz,marks_length])
    (by simp [c,b,a,Control.copySt,rn (show (2 : Fin 4)≠1 by decide),
      rn (show (2 : Fin 4)≠0 by decide),hz])
    (by simp [c,b,a,Control.copySt,rn (show (3 : Fin 4)≠1 by decide),
      rn (show (3 : Fin 4)≠0 by decide),hz]) (by omega)
  refine (ec.seq (eb.seq ((WXExec.wm er).seq (WXExec.wm ef)))).cast cap ?_ (by omega)
  apply WState.eq
  · funext i
    by_cases hi : i=src
    · subst i;simp [c,b,a,Control.copySt,hsd]
    · by_cases ho : i=dst
      · subst i;simp
      · simp [c,b,a,Control.copySt,Function.update_of_ne hi,Function.update_of_ne ho]
  · funext i
    by_cases hi : i=dst
    · subst i;simp
    · simp [c,b,a,Control.copySt,Function.update_of_ne hi]
  · funext i
    by_cases hi : i=R 0
    · subst i;simp [c,b,a,Control.copySt,rn (show (0 : Fin 4)≠1 by decide),hz,marks_length]
    · by_cases ho : i=R 1
      · subst i;simp [c,b,a,Control.copySt,hi,hz]
      · simp [c,b,a,Control.copySt,hi,ho]
  · rfl

end NearQuarticWires.StageCertificateControl
