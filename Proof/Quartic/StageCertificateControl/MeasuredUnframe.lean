import Proof.Quartic.StageCertificateControl.RawReturn
import Proof.Gates.Codec.Unframe

/-!
# Unframe metadata using its measured copy distance

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

/-- `prop:time`, paper/paper.tex: the
entire measured payload is exactly the original binary word. -/
theorem measuredPrefix_self (bits : List Bool) : Codec.prefixBits bits bits.length=bits := by
  apply List.ext_getElem
  · simp [Codec.prefixBits]
  · intro n h1 h2
    simp [Codec.prefixBits,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h2]

/-- `prop:time`, paper/paper.tex: the actual
marked-byte count is copied and halved before the counted unframing
loop. The preserved count is not a supplied output-length oracle. -/
def measuredUnframe (src dst : Fin (ns+1)) (R : Fin 6 ↪ Fin nr) : WM ns nr :=
  .seq (NearCubicWires.WireExponent3_5.FinalPass.Hash4.wcopyR (R 0) (R 1) (R 2))
    (.seq (halveM (R 1) (R 3) (R 4)) (Codec.unframeW src dst (R 5) (R 1)))

/-- `prop:time`, paper/paper.tex: the actual
unframing preserves the original marked count, restores every scratch
register, and charges a linear number of instructions in payload bits. -/
theorem measuredUnframe_spec (cap : ℕ) (src dst : Fin (ns+1)) (hsd : src≠dst)
    (R : Fin 6 ↪ Fin nr) (bits : List Bool) (σ : WState ns nr)
    (hs : σ.st src=frame bits) (hsh : σ.sh src=0)
    (hd : σ.sh dst=(σ.st dst).length) (hOP : σ.val (R 0)=2*bits.length)
    (h1 : σ.val (R 1)=0) (h2 : σ.val (R 2)=0)
    (h3 : σ.val (R 3)=0) (h4 : σ.val (R 4)=0)
    (hcap : 2*bits.length+2≤cap) (hraw : σ.val (R 5)+bits.length≤cap) :
    WExec cap (measuredUnframe src dst R) σ
      ((appendO σ dst (R 5) bits).seth src (2*bits.length)) (100*bits.length+50) := by
  have rn {i j : Fin 6} (h : i≠j) : R i≠R j := R.injective.ne h
  have ec := NearCubicWires.WireExponent3_5.FinalPass.Hash4.wcopyR_spec cap
    (R 0) (R 1) (R 2) (rn (by decide)) (rn (by decide)) (rn (by decide)) σ h1 h2
    (by rw [hOP];omega)
  rw [hOP] at ec
  let a := σ.setv (R 1) (2*bits.length)
  have eh := halveM_spec cap (R 1) (R 3) (R 4)
    (rn (by decide)) (rn (by decide)) (rn (by decide)) a
    (by simp [a,Function.update_of_ne (rn (show (3 : Fin 6)≠1 by decide)),h3])
    (by simp [a,Function.update_of_ne (rn (show (4 : Fin 6)≠1 by decide)),h4])
    (by simp [a];omega) (by omega)
  let b := σ.setv (R 1) bits.length
  have hend : (a.setv (R 1) (a.val (R 1)/2)).setv (R 4) (a.val (R 1)%2)=b := by
    simp only [a,WState.setv_val,Function.update_self,Nat.mul_div_right,Nat.mul_mod_right]
    rw [wsetv_setv]
    apply WState.eq
    · rfl
    · rfl
    · funext i
      by_cases hi : i=R 4
      · subst i;simp [b,Function.update_of_ne (rn (show (4 : Fin 6)≠1 by decide)),h4]
      · simp [b,Function.update_of_ne hi]
    · rfl
  rw [hend] at eh
  have eu := Codec.unframeW_spec cap src dst hsd (R 5) (R 1) (rn (by decide)) bits
    bits.length b hs hsh hd (by simp [b]) (by omega)
    (by simpa only [b,WState.setv_val,Function.update_of_ne (rn (show (5 : Fin 6)≠1 by decide))] using hraw)
  rw [measuredPrefix_self,Nat.min_self] at eu
  refine (ec.seq (eh.seq eu)).cast cap ?_ ?_
  · apply WState.eq
    · simp [b,appendO]
    · simp [b,appendO]
    · funext i
      by_cases hi : i=R 1
      · subst i;simp [appendO,rn (show (1 : Fin 6)≠5 by decide),h1]
      · by_cases ho : i=R 5
        · subst i;simp [b,appendO,hi]
        · simp [b,appendO,hi,ho]
    · rfl
  · simp [a]
    omega

end NearQuarticWires.StageCertificateControl
