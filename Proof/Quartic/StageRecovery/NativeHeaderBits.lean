import Proof.Quartic.StageRecovery.NativeRequest
import Proof.Gates.CounterMachine.PrefixMac

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms

/-- `lem:print`, paper/paper.tex: the existing
unary-prefix reader also applies before a literal false delimiter and
payload, preserving the entire actual encoded source stream. -/
theorem leadingUnaryRegister_spec {ns nr : ℕ} (cap : ℕ) (S : Fin (ns + 1))
    (C R : Fin nr) (hCR : C ≠ R) (σ : WState ns nr) (n : ℕ) (rest : List Bool)
    (hS : σ.st S = List.replicate n true ++ false :: rest)
    (hSh : σ.sh S = 0) (hC : σ.val C = 0) (hR : σ.val R = 0) (hn : n + 1 ≤ cap) :
    WXExec cap (StagePrint.unaryRegister S C R) σ (σ.setv R n) (16 * n + 14) := by
  have htrue : ∀ k < n, readTapeBit (σ.st S) (σ.sh S + k) = true := by
    intro k hk
    simp only [readTapeBit, hS, hSh, Nat.zero_add]
    rw [List.getD_append _ _ _ _ (by simpa using hk)]
    simp [hk]
  have hfalse : readTapeBit (σ.st S) (σ.sh S + n) = false := by
    simp only [readTapeBit, hS, hSh, Nat.zero_add]
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp
  have e1 := wreadU_spec cap S C R hCR n σ htrue hfalse (by omega) (by omega)
  let τ := ((σ.seth S (σ.sh S + n + 1)).setv C (σ.val C + n + 1)).setv R (σ.val R + n)
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

/-- `lem:print`, paper/paper.tex: the modulus's
actual binary length is read from its canonical codec prefix without
ever decoding the potentially large modulus as a unary value. -/
theorem natWordBitLength_spec {ns nr : ℕ} (cap : ℕ) (S : Fin (ns + 1))
    (C R : Fin nr) (hCR : C ≠ R) (σ : WState ns nr) (value : ℕ)
    (hS : σ.st S = RepairRepresentation.natWord value)
    (hSh : σ.sh S = 0) (hC : σ.val C = 0) (hR : σ.val R = 0)
    (hn : natBitLength value + 1 ≤ cap) :
    WXExec cap (StagePrint.unaryRegister S C R) σ (σ.setv R (natBitLength value))
      (16 * natBitLength value + 14) := by
  apply leadingUnaryRegister_spec cap S C R hCR σ (natBitLength value)
    (RepairOrdinary.SignedSortKey.binary (natBitLength value) value) ?_ hSh hC hR hn
  rw [hS, NearCubicGates.Close.CounterMachine.PrefixProg.natWord_bin]

end NearQuarticWires.StageRecovery
