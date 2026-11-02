import Proof.Quartic.StageCertificateControl.MeasuredUnframe

/-!
# Open a physically copied frame using its actual output counter

Paper: `prop:time`, paper/paper.tex.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close

variable {ns nr : ℕ}

/-- `prop:time`, paper/paper.tex: a copied
frame is returned by its real output counter; subtracting its one
terminal bit leaves the measured marked-payload length. -/
def returnCopiedFrame (src : Fin (ns+1)) (OP tmp scratch : Fin nr) : WM ns nr :=
  .seq (NearCubicWires.WireExponent3_5.FinalPass.Hash4.wcopyR OP tmp scratch)
    (.seq (WM.rewind src tmp) (.dec OP))

/-- `prop:time`, paper/paper.tex: the actual
copied-frame head returns to zero, its terminal bit is removed from the
count, and both temporary registers are restored exactly. -/
theorem returnCopiedFrame_spec (cap : ℕ) (src : Fin (ns+1)) (OP tmp scratch : Fin nr)
    (hOt : OP≠tmp) (hOs : OP≠scratch) (hts : tmp≠scratch)
    (bits : List Bool) (σ : WState ns nr)
    (hsh : σ.sh src=(frame bits).length) (hOP : σ.val OP=(frame bits).length)
    (ht : σ.val tmp=0) (hs : σ.val scratch=0)
    (hcap : (frame bits).length+2≤cap) :
    WExec cap (returnCopiedFrame src OP tmp scratch) σ
      ((σ.setv OP (2*bits.length)).seth src 0) (50*bits.length+50) := by
  have hl : (frame bits).length=2*bits.length+1 := by simp [Codec.frame_eq_marks]
  have ec := NearCubicWires.WireExponent3_5.FinalPass.Hash4.wcopyR_spec cap
    OP tmp scratch hOt hOs hts σ ht hs (by rw [hOP];omega)
  rw [hOP] at ec
  let a := σ.setv tmp (frame bits).length
  have er := wrewind_spec cap src tmp (frame bits).length a (by simp [a])
    (by simp [a];omega)
  let b := (a.setv tmp 0).seth src (a.sh src-(frame bits).length)
  have ed := WExec.dec (cap := cap) OP b (by simp [b,a,Function.update_of_ne hOt,hOP];omega)
  refine (ec.seq (er.seq ed)).cast cap ?_ ?_
  · apply WState.eq
    · funext i
      by_cases hi : i=src
      · subst i;simp [b,a,hsh]
      · simp [b,a,Function.update_of_ne hi]
    · rfl
    · funext i
      by_cases hi : i=OP
      · subst i;simp [b,a,Function.update_of_ne hOt,hOP,hl]
      · by_cases ht' : i=tmp
        · subst i;simp [b,a,Function.update_of_ne hOt.symm,ht]
        · simp [b,a,Function.update_of_ne hi,Function.update_of_ne ht']
    · rfl
  · simp [hl]
    omega

/-- `prop:time`, paper/paper.tex: the exact
raw metadata stream is recovered from the actual copied frame by paid
head returns, terminal accounting, halving and binary unframing. -/
def openCopiedFrame (src dst : Fin (ns+1)) (R : Fin 6 ↪ Fin nr) : WM ns nr :=
  .seq (returnCopiedFrame src (R 0) (R 1) (R 2)) (measuredUnframe src dst R)

/-- `prop:time`, paper/paper.tex: opening
the actual copied frame costs only its binary length and retains every
source bit, without any externally supplied output length. -/
theorem openCopiedFrame_spec (cap : ℕ) (src dst : Fin (ns+1)) (hsd : src≠dst)
    (R : Fin 6 ↪ Fin nr) (bits : List Bool) (σ : WState ns nr)
    (hs : σ.st src=frame bits) (hsh : σ.sh src=(frame bits).length)
    (hd : σ.sh dst=(σ.st dst).length) (hOP : σ.val (R 0)=(frame bits).length)
    (h1 : σ.val (R 1)=0) (h2 : σ.val (R 2)=0)
    (h3 : σ.val (R 3)=0) (h4 : σ.val (R 4)=0)
    (hcap : (frame bits).length+2≤cap) (hraw : σ.val (R 5)+bits.length≤cap) :
    WExec cap (openCopiedFrame src dst R) σ
      ((appendO (σ.setv (R 0) (2*bits.length)) dst (R 5) bits).seth src (2*bits.length))
      (200*bits.length+150) := by
  have rn {i j : Fin 6} (h : i≠j) : R i≠R j := R.injective.ne h
  have er := returnCopiedFrame_spec cap src (R 0) (R 1) (R 2)
    (rn (by decide)) (rn (by decide)) (rn (by decide)) bits σ hsh hOP h1 h2 hcap
  let a := (σ.setv (R 0) (2*bits.length)).seth src 0
  have eu := measuredUnframe_spec cap src dst hsd R bits a hs (by simp [a])
    (by simp [a,Function.update_of_ne hsd.symm,hd]) (by simp [a])
    (by simp [a,rn (show (1 : Fin 6)≠0 by decide),h1])
    (by simp [a,rn (show (2 : Fin 6)≠0 by decide),h2])
    (by simp [a,rn (show (3 : Fin 6)≠0 by decide),h3])
    (by simp [a,rn (show (4 : Fin 6)≠0 by decide),h4])
    (by simp [Codec.frame_eq_marks] at hcap;omega)
    (by simpa [a,rn (show (5 : Fin 6)≠0 by decide)] using hraw)
  refine (er.seq eu).cast cap ?_ (by omega)
  apply WState.eq
  · funext i
    by_cases hi : i=src
    · subst i;simp [a,appendO,hsd]
    · by_cases ho : i=dst
      · subst i;simp [a,appendO,hsd.symm,hi]
      · simp [a,appendO,Function.update_of_ne hi,Function.update_of_ne ho]
  · simp [a,appendO]
  · simp [a,appendO]
  · rfl

end NearQuarticWires.StageCertificateControl
