import Proof.Quartic.Sampler.Fourier
import Proof.Quartic.Cells.Score

set_option autoImplicit false

namespace NearQuarticWires.Sampler

open Finset
open NearCubicWires NearCubicWires.WireExponent3_5.Shared

/-- `lem:fourier`, paper/paper.tex: a Boolean bit as a complex scalar. -/
def boolBit (b : Bool) : ℂ := if b then 1 else 0

/-- `lem:fourier`, paper/paper.tex: a bit has modulus at most one. -/
theorem norm_boolBit_le (b : Bool) : ‖boolBit b‖ ≤ 1 := by cases b <;> simp [boolBit]

/-- `lem:fourier`, paper/paper.tex: actual bounded-score extension,
zero OUTSIDE the original circuit-score box. Single calls have G₂=0. -/
noncomputable def lookupExtension (m G₁ G₂ : ℕ) (g : ℕ × ℕ → Bool)
    (t : Frequency m G₁ G₂) : ℂ :=
  if t.1.val ≤ G₁ ∧ t.2.val ≤ G₂ then boolBit (g (t.1.val, t.2.val)) else 0

/-- `lem:fourier`, paper/paper.tex: the ACTUAL lookup extension
meets the Parseval boundedness hypothesis, including outside-box zero values. -/
theorem norm_lookupExtension_le (m G₁ G₂ : ℕ) (g : ℕ × ℕ → Bool)
    (t : Frequency m G₁ G₂) : ‖lookupExtension m G₁ G₂ g t‖ ≤ 1 := by
  unfold lookupExtension
  split_ifs
  · exact norm_boolBit_le _
  · simp

/-- `lem:fourier`, paper/paper.tex: no score wraps at modulus 4mG+1. -/
theorem omega_gt_score {m G : ℕ} (hm : 1 ≤ m) : G < omega m G := by
  unfold omega
  nlinarith

/-- `lem:fourier`, paper/paper.tex: exact evaluation on a real
cell's integer score; outside-box extension introduces no alias. -/
theorem lookupExtension_cast {m G₁ G₂ : ℕ} (hm : 1 ≤ m)
    (g : ℕ × ℕ → Bool) (s₁ s₂ : ℤ)
    (hs₁ : 0 ≤ s₁ ∧ s₁ ≤ G₁) (hs₂ : 0 ≤ s₂ ∧ s₂ ≤ G₂) :
    lookupExtension m G₁ G₂ g
      ((s₁ : ZMod (omega m G₁)), (s₂ : ZMod (omega m G₂))) =
      boolBit (g (s₁.toNat, s₂.toNat)) := by
  have hval₁ : ((s₁ : ZMod (omega m G₁)).val : ℤ) = s₁ := by
    rw [ZMod.val_intCast]
    exact Int.emod_eq_of_lt hs₁.1 (lt_of_le_of_lt hs₁.2 (by exact_mod_cast omega_gt_score hm))
  have hval₂ : ((s₂ : ZMod (omega m G₂)).val : ℤ) = s₂ := by
    rw [ZMod.val_intCast]
    exact Int.emod_eq_of_lt hs₂.1 (lt_of_le_of_lt hs₂.2 (by exact_mod_cast omega_gt_score hm))
  have hv₁ : (s₁ : ZMod (omega m G₁)).val = s₁.toNat := by omega
  have hv₂ : (s₂ : ZMod (omega m G₂)).val = s₂.toNat := by omega
  have hb₁ : s₁.toNat ≤ G₁ := by omega
  have hb₂ : s₂.toNat ≤ G₂ := by omega
  simp [lookupExtension, hv₁, hv₂, hb₁, hb₂]

/-- `lem:fourier`, paper/paper.tex: actual product-star call
decomposition on occurrence LISTS (duplicates retained), with the exact cells
score/residual definitions, modulus 4mG+1, and mask INSIDE each residual matrix. -/
theorem cell_fourier_decomposition {N : ℕ} (P : StarParams) (m : ℕ) (hm : 1 ≤ m)
    (gates₁ gates₂ : List (NormalizedThresholdGate P.n)) (g : ℕ × ℕ → Bool)
    (c : BitInput P.n) (e : Fin N → P.Errors) (mask : Cell N → ℝ) (u v : Fin N) :
    boolBit (g ((NearQuarticWires.Cells.score P gates₁ c (e u) (e v)).toNat,
      (NearQuarticWires.Cells.score P gates₂ c (e u) (e v)).toNat)) *
      (mask (u, v) : ℂ) =
    ∑ θ : Frequency m gates₁.length gates₂.length,
      coefficient (lookupExtension m gates₁.length gates₂.length g) θ *
      phase θ (NearQuarticWires.Cells.scoreLeft P gates₁ c (e u))
        (NearQuarticWires.Cells.scoreLeft P gates₂ c (e u)) *
      phase θ (NearQuarticWires.Cells.scoreRight P gates₁ c (e v))
        (NearQuarticWires.Cells.scoreRight P gates₂ c (e v)) *
      maskedPhase θ
        (fun x => NearQuarticWires.Cells.residual P gates₁ c (e x.1) (e x.2))
        (fun x => NearQuarticWires.Cells.residual P gates₂ c (e x.1) (e x.2))
        mask (u, v) := by
  rw [← lookupExtension_cast hm g _ _
    (NearQuarticWires.Cells.score_bounds P gates₁ c (e u) (e v))
    (NearQuarticWires.Cells.score_bounds P gates₂ c (e u) (e v))]
  rw [NearQuarticWires.Cells.score_identity, NearQuarticWires.Cells.score_identity]
  exact masked_score_decomposition (m := m) (G₁ := gates₁.length)
    (G₂ := gates₂.length) (N := N)
    (lookupExtension m gates₁.length gates₂.length g)
    (fun i => NearQuarticWires.Cells.scoreLeft P gates₁ c (e i))
    (fun i => NearQuarticWires.Cells.scoreLeft P gates₂ c (e i))
    (fun i => NearQuarticWires.Cells.scoreRight P gates₁ c (e i))
    (fun i => NearQuarticWires.Cells.scoreRight P gates₂ c (e i))
    (fun x => NearQuarticWires.Cells.residual P gates₁ c (e x.1) (e x.2))
    (fun x => NearQuarticWires.Cells.residual P gates₂ c (e x.1) (e x.2))
    mask u v

end NearQuarticWires.Sampler
