import Proof.Quartic.Cycle.ConditionalIdentity
import Proof.Quartic.Sampler.CycleDock

set_option autoImplicit false

namespace NearQuarticWires.Cycle
open Finset
open NearQuarticWires.Sampler
open NearCubicWires.WireExponent3_5.Shared (uMean)
open NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.WireExponent3_5.Sampler

/-- Paper `cor:conditional`: the actual integer seed of length S,
with all 2^S possibilities retained. -/
noncomputable def finiteSeed (P : SeedParameters) (s : Fin (2^(seedLength P))) : P.Seed :=
  decodeNat P s

/-- Paper `cor:conditional`: S bits enumerate the eight field
coefficients bijectively, so the empty-prefix mean is the generator mean. -/
theorem finiteSeed_bijective (P : SeedParameters) : Function.Bijective (finiteSeed P) := by
  rw [Fintype.bijective_iff_surjective_and_card]
  constructor
  · intro c
    obtain ⟨s, hs⟩ := (seedOfBits_bijective P).surjective c
    refine ⟨⟨ofBits s, ?_⟩, hs⟩
    exact ofVec_lt _
  · rw [Fintype.card_fin, SeedParams.card_seed]
    rfl

/-- Paper `cor:conditional`: eight-wise independence suffices for
the FULL actual dilation potential, with its signed Γ factors. -/
theorem mean_columnPotential_seed {G₁ G₂ : ℕ} (P : SeedParameters)
    (R₁ R₂ : Cell P.N → ℤ) (mask : Cell P.N → ℝ) :
    uMean (fun c : P.Seed => columnPotential (G₁ := G₁) (G₂ := G₂)
      R₁ R₂ mask (P.pos c)) =
    uMean (fun S : Fin P.Q → Cell P.N => columnPotential (G₁ := G₁) (G₂ := G₂)
      R₁ R₂ mask S) := by
  let D := matrixDictionary (G₁ := G₁) (G₂ := G₂)
    (fun _ : Unit => R₁) (fun _ : Unit => R₂) (fun _ : Unit => mask)
  have hd (S : Fin P.Q → Cell P.N) :
      columnPotential (G₁ := G₁) (G₂ := G₂) R₁ R₂ mask S =
        2 * NearCubicWires.WireExponent3_5.Sampler.potential D S := by
    have h := paperPotential_eq_sum_columnPotential
      (G₁ := G₁) (G₂ := G₂) (fun _ : Unit => R₁) (fun _ : Unit => R₂)
      (fun _ : Unit => mask) S
    simpa only [paperPotential, halfPotential, Finset.univ_unique,
      Finset.sum_singleton] using h.symm
  simp_rw [hd]
  rw [uMean_const_mul, uMean_const_mul, uMean_potential_seed P D]

/-- Paper `cor:conditional`: the empty-prefix conditional mean
is EXACTLY the independent-uniform sample mean, not merely an upper bound. -/
theorem conditionalPotential_empty {G₁ G₂ : ℕ} (P : SeedParameters)
    (R₁ R₂ : Cell P.N → ℤ) (mask : Cell P.N → ℝ) :
    conditionalPotential (G₁ := G₁) (G₂ := G₂) P R₁ R₂ mask 0 0 =
      uMean (fun S : Fin P.Q → Cell P.N => columnPotential (G₁ := G₁) (G₂ := G₂)
        R₁ R₂ mask S) := by
  have hn : conditionalPotential (G₁ := G₁) (G₂ := G₂) P R₁ R₂ mask 0 0 =
      uMean (fun s : Fin (2^(seedLength P)) => columnPotential (G₁ := G₁) (G₂ := G₂)
        R₁ R₂ mask (P.pos (finiteSeed P s))) := by
    unfold conditionalPotential uMean
    simp only [Nat.sub_zero, completion, Nat.pow_zero, Nat.zero_mod,
      Nat.shiftLeft_zero, zero_add, Fintype.card_fin]
    simp only [seedSample, finiteSeed]
    rw [← Fin.sum_univ_eq_sum_range]
    norm_cast
  rw [hn]
  have hm : uMean (fun s : Fin (2^(seedLength P)) => columnPotential
      (G₁ := G₁) (G₂ := G₂) R₁ R₂ mask (P.pos (finiteSeed P s))) =
      uMean (fun c : P.Seed => columnPotential (G₁ := G₁) (G₂ := G₂)
        R₁ R₂ mask (P.pos c)) := by
    unfold uMean
    rw [Fintype.card_congr (Equiv.ofBijective _ (finiteSeed_bijective P))]
    congr 1
    exact Function.Bijective.sum_comp (finiteSeed_bijective P)
      (fun c => columnPotential (G₁ := G₁) (G₂ := G₂) R₁ R₂ mask (P.pos c))
  rw [hm, mean_columnPotential_seed P R₁ R₂ mask]

#print axioms conditionalPotential_empty
end NearQuarticWires.Cycle
