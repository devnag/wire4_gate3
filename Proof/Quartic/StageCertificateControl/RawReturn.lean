import Proof.Quartic.StageCertificateControl.RawFields

/-!
# Return a raw metadata source using its actual marked-byte count

Paper: `prop:time`, paper/paper.tex.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat

variable {ns nr : ℕ}

/-- `prop:time`, paper/paper.tex: a marked
copy records twice the raw source distance. A preserved counter copy
is halved and consumed by the actual backward-head loop. -/
def returnRawSource (src : Fin (ns+1)) (R : Fin 5 ↪ Fin nr) : WM ns nr :=
  .seq (NearCubicWires.WireExponent3_5.FinalPass.Hash4.wcopyR (R 0) (R 1) (R 2))
    (.seq (halveM (R 1) (R 3) (R 4)) (WM.rewind src (R 1)))

/-- `prop:time`, paper/paper.tex: the raw
source returns exactly to its original offset by charged instructions.
The true marked-byte counter is retained, all scratch is restored,
and no threshold value or output-length oracle is used. -/
theorem returnRawSource_spec (cap : ℕ) (src : Fin (ns+1)) (R : Fin 5 ↪ Fin nr)
    (σ : WState ns nr) (base bytes : ℕ) (hsh : σ.sh src=base+bytes)
    (hOP : σ.val (R 0)=2*bytes) (h1 : σ.val (R 1)=0) (h2 : σ.val (R 2)=0)
    (h3 : σ.val (R 3)=0) (h4 : σ.val (R 4)=0) (hcap : 2*bytes+2≤cap) :
    WExec cap (returnRawSource src R) σ (σ.seth src base) (60*bytes+20) := by
  have rn {i j : Fin 5} (h : i≠j) : R i≠R j := R.injective.ne h
  have ec := NearCubicWires.WireExponent3_5.FinalPass.Hash4.wcopyR_spec cap
    (R 0) (R 1) (R 2) (rn (by decide)) (rn (by decide)) (rn (by decide)) σ h1 h2 (by rw [hOP];omega)
  rw [hOP] at ec
  let a := σ.setv (R 1) (2*bytes)
  have eh := halveM_spec cap (R 1) (R 3) (R 4) (rn (by decide)) (rn (by decide)) (rn (by decide)) a
    (by simp [a,Function.update_of_ne (rn (show (3 : Fin 5)≠1 by decide)),h3])
    (by simp [a,Function.update_of_ne (rn (show (4 : Fin 5)≠1 by decide)),h4])
    (by simp [a];omega) (by omega)
  let b := a.setv (R 1) bytes
  have hend : (a.setv (R 1) (a.val (R 1)/2)).setv (R 4) (a.val (R 1)%2)=b := by
    simp only [a,WState.setv_val,Function.update_self,Nat.mul_div_right,Nat.mul_mod_right]
    rw [wsetv_setv]
    apply WState.eq
    · rfl
    · rfl
    · funext i
      by_cases hi : i=R 4
      · subst i;simp [b,a,Function.update_of_ne (rn (show (4 : Fin 5)≠1 by decide)),h4]
      · simp [b,a,Function.update_of_ne hi]
    · rfl
  rw [hend] at eh
  have er := wrewind_spec cap src (R 1) bytes b (by simp [b]) (by simp [b];omega)
  refine (ec.seq (eh.seq er)).cast cap ?_ ?_
  · apply WState.eq
    · funext i
      by_cases hi : i=src
      · subst i;simp [b,a,hsh]
      · simp [b,a,Function.update_of_ne hi]
    · rfl
    · funext i
      by_cases hi : i=R 1
      · subst i;simp [h1]
      · simp [b,a,Function.update_of_ne hi]
    · rfl
  · simp [a]
    omega

end NearQuarticWires.StageCertificateControl
