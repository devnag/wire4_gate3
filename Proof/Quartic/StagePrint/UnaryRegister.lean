import Proof.Quartic.StagePrint.CutTables
import Proof.Wire_3_5.PrimAsmSymDecStreams

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: read a unary table dimension while returning the source head to zero. -/
def unaryRegister (S : Fin (ns + 1)) (C R : Fin nr) : WMX ns nr :=
  .seq (.wm (WM.readU S C R)) (.wm (WM.rewind S C))

/-- `lem:print`, paper/paper.tex: the table-dimension read preserves its encoded stream. -/
theorem unaryRegister_spec (cap : ℕ) (S : Fin (ns + 1)) (C R : Fin nr) (hCR : C ≠ R)
    (σ : WState ns nr) (n : ℕ) (hS : σ.st S = List.replicate n true)
    (hSh : σ.sh S = 0) (hC : σ.val C = 0) (hR : σ.val R = 0) (hn : n + 1 ≤ cap) :
    WXExec cap (unaryRegister S C R) σ (σ.setv R n) (16 * n + 14) := by
  have e1 := wreadU_spec cap S C R hCR n σ
    (by intro k hk; rw [hS, hSh]; simp [readTapeBit, hk])
    (by rw [hS, hSh]; simp [readTapeBit]) (by omega) (by omega)
  set τ := ((σ.seth S (σ.sh S + n + 1)).setv C (σ.val C + n + 1)).setv R (σ.val R + n)
  have e2 := wrewind_spec cap S C (n + 1) τ
    (by simp [τ, hC, Function.update_of_ne hCR])
    (by simp [τ, hC, Function.update_of_ne hCR]; omega)
  refine (WXExec.seq (WXExec.wm e1) (WXExec.wm e2)).cast cap ?_ (by omega)
  apply WState.eq
  · funext i
    by_cases hi : i = S
    · subst hi; simp [τ, hSh]
    · simp [τ, Function.update_of_ne hi]
  · rfl
  · funext i
    by_cases hi : i = C
    · subst hi; simp [τ, hC, Function.update_of_ne hCR, Function.update_of_ne (Ne.symm hCR)]
    · by_cases hiR : i = R
      · subst hiR; simp [τ, hR, hi]
      · simp [τ, Function.update_of_ne hi, Function.update_of_ne hiR]
  · rfl

end NearQuarticWires.StagePrint
