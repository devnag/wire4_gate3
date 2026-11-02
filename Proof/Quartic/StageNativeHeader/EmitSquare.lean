import Proof.Quartic.StageNativeHeader.EmitNums

/-!
# The emission: `U = 2^d` and the field of `U²` ones

Paper: `lem:print`, paper/paper.tex.

`uPhase`: `U = 2^d` by `d` doublings. `sqPhase`: `U` rounds, each copying `U` into a counter and appending `U` ones
at depth two, append `U²` ones at depth two (`emit_unary2_mul`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearQuarticWires.StageNativeHeader

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (addTo addTo_spec dbl dbl_spec)
open NearQuarticWires.Control

variable (cap : ℕ)

theorem emit_unary2_add (a b : ℕ) : unary2 (a + b) = unary2 a ++ unary2 b := by
  unfold unary2; rw [List.replicate_add, List.flatten_append]

theorem emit_unary2_mul (a b : ℕ) : (List.replicate a (unary2 b)).flatten = unary2 (a * b) := by
  induction a with
  | zero => simp [unary2]
  | succ a ih => rw [List.replicate_succ, List.flatten_cons, ih, Nat.succ_mul, Nat.add_comm (a * b) b, emit_unary2_add]

/-! ## `U = 2^d` -/

/-- `rU := 2^d` (`rK1` counts the doublings). -/
noncomputable def uP : WM hns hnr :=
  .seq (.inc rU) (.seq (addTo rD rK1 rTmp) (runLoop rK1 (dbl rU rTmp)))

theorem uPhase (σ : WState hns hnr) (d : ℕ) (hd : σ.val rD = d) (hU : σ.val rU = 0) (hK : σ.val rK1 = 0)
    (hT : σ.val rTmp = 0) (hcap : 2 * 2 ^ d + d + 1 ≤ cap) (ho : σ.sh sACC = (σ.st sACC).length)
    (hop : σ.val eOP ≤ cap) :
    ∃ τ, WExec cap uP σ τ (d * (18 * 2 ^ d + 7) + 18 * d + 12) ∧ Emitted σ τ [] [rK1, rU] [] ∧
      τ.val rU = 2 ^ d ∧ τ.val rTmp = 0 := by
  have h1 : 1 ≤ 2 ^ d := Nat.one_le_two_pow
  have e1 := WExec.inc (cap := cap) rU σ (by rw [hU]; omega)
  set σ1 := σ.setv rU (σ.val rU + 1) with hσ1
  have e2 := addTo_spec cap rD rK1 rTmp (by decide) (by decide) (by decide) σ1
    (by simp (config := { decide := true }) [hσ1, hT]) (by simp (config := { decide := true }) [hσ1, hd]; omega)
    (by simp (config := { decide := true }) [hσ1, hd, hK]; omega)
  set σ2 := σ1.setv rK1 (σ1.val rK1 + σ1.val rD) with hσ2
  have k2 : σ2.val rK1 = d := by simp (config := { decide := true }) [hσ2, hσ1, hd, hK]
  have m12 : Emitted σ σ2 [] [rK1, rU] [] :=
    (((emitted_setv σ rU _ (by decide)).weaken (L' := [rK1, rU]) (by decide) (fun _ h => h)).trans
      ((emitted_setv σ1 rK1 _ (by decide)).weaken (L' := [rK1, rU]) (by decide) (fun _ h => h))).equ (by simp)
  obtain ⟨τ, e3, m3, ⟨p3T, p3U⟩, k3⟩ := repEmit cap rK1 (by decide) (dbl rU rTmp) [] (18 * 2 ^ d + 3) [rU] []
    (by decide) d (fun i σ => σ.val rTmp = 0 ∧ σ.val rU = 2 ^ i)
    (fun i σ x ⟨a, b⟩ => ⟨by simp (config := { decide := true }) [a], by simp (config := { decide := true }) [b]⟩)
    (fun i hi σ ⟨a, b⟩ _ _ => by
      have hpow : 2 * 2 ^ i ≤ 2 ^ d := by
        rw [← pow_succ']; exact Nat.pow_le_pow_right (by norm_num) hi
      refine ⟨_, WExec.mono (dbl_spec cap rU rTmp (by decide) σ a (by rw [b]; omega)) (by rw [b]; omega),
        emitted_setv σ rU _ (by decide), by simp (config := { decide := true }) [a], ?_⟩
      simp only [WState.setv_val, Function.update_self, b]; ring)
    σ2 k2 ⟨by simp (config := { decide := true }) [hσ2, hσ1, hT], by simp (config := { decide := true }) [hσ2, hσ1, hU]⟩
    (by simpa [hσ2, hσ1] using ho) (by simp (config := { decide := true }) [hσ2, hσ1]; omega) (by omega)
  refine ⟨τ, WExec.mono (WExec.seq e1 (WExec.seq e2 e3)) (by simp (config := { decide := true }) [hσ1, hd]; ring_nf; omega),
    (m12.trans (m3.weaken (by decide) (fun _ h => h))).equ (by simp), p3U, p3T⟩

/-! ## `U²` ones at depth two -/

/-- `U` rounds of `U` ones at depth two. -/
noncomputable def sqP : WM hns hnr :=
  .seq (addTo rU eK2 rTmp) (runLoop eK2 (.seq (addTo rU eK3 rTmp) (unaryP eK3)))

theorem sqPhase (σ : WState hns hnr) (U : ℕ) (hU : σ.val rU = U) (hK2 : σ.val eK2 = 0) (hK3 : σ.val eK3 = 0)
    (hT : σ.val rTmp = 0) (ho : σ.sh sACC = (σ.st sACC).length) (hc : σ.val eOP + 4 * (U * U) ≤ cap)
    (hUc : 2 * U ≤ cap) :
    ∃ τ, WExec cap sqP σ τ (U * (54 * U + 9) + 18 * U + 5) ∧ Emitted σ τ (unary2 (U * U)) [eK2, eK3] [] := by
  have e1 := addTo_spec cap rU eK2 rTmp (by decide) (by decide) (by decide) σ hT (by omega) (by rw [hU, hK2]; omega)
  set σ1 := σ.setv eK2 (σ.val eK2 + σ.val rU) with hσ1
  obtain ⟨τ, e2, m2, -, -⟩ := repEmit cap eK2 (by decide) (.seq (addTo rU eK3 rTmp) (unaryP eK3)) (unary2 U)
    (54 * U + 5) [eK3] [] (by decide) U
    (fun _ σ => σ.val rTmp = 0 ∧ σ.val eK3 = 0 ∧ σ.val rU = U)
    (fun i σ x ⟨a, b, c⟩ => ⟨by simp (config := { decide := true }) [a], by simp (config := { decide := true }) [b],
      by simp (config := { decide := true }) [c]⟩)
    (fun i hi σ ⟨a, b, c⟩ ho' hc' => by
      have f1 := addTo_spec cap rU eK3 rTmp (by decide) (by decide) (by decide) σ a (by omega) (by rw [b, c]; omega)
      set σ' := σ.setv eK3 (σ.val eK3 + σ.val rU) with hσ'
      have hlen : (unary2 U).length = 4 * U := by simp [unary2]; ring
      obtain ⟨τ', f2, m2', k2'⟩ := unaryPhase cap eK3 (by decide) U σ' (by simp [hσ', b, c])
        (by simpa [hσ'] using ho') (by simp (config := { decide := true }) [hσ']; omega) (by omega)
      refine ⟨τ', WExec.mono (WExec.seq f1 f2) (by rw [c]; omega), ?_, ?_, k2', ?_⟩
      · exact ((emitted_setv σ eK3 _ (by decide)).trans m2').equ (by simp)
      · rw [m2'.val rTmp (by decide) (by decide)]; simp (config := { decide := true }) [hσ', a]
      · rw [m2'.val rU (by decide) (by decide)]; simp (config := { decide := true }) [hσ', c])
    σ1 (by simp (config := { decide := true }) [hσ1, hU, hK2])
    ⟨by simp (config := { decide := true }) [hσ1, hT], by simp (config := { decide := true }) [hσ1, hK3],
      by simp (config := { decide := true }) [hσ1, hU]⟩
    (by simpa [hσ1] using ho)
    (by
      have hlen : (unary2 U).length = 4 * U := by simp [unary2]; ring
      simp (config := { decide := true }) [hσ1]; rw [hlen]; nlinarith) (by omega)
  refine ⟨τ, WExec.mono (WExec.seq e1 e2) (by rw [hU]; ring_nf; omega), ?_⟩
  have := ((emitted_setv σ eK2 _ (by decide)).weaken (L' := [eK2, eK3]) (by decide) (fun _ h => h)).trans m2
  exact this.equ (by rw [List.nil_append, emit_unary2_mul])

end NearQuarticWires.StageNativeHeader
