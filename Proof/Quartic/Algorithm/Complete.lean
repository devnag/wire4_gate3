import Proof.Quartic.Algorithm.Sound

/-!
# Completeness of the counting algorithm (`prop:complete`)

Paper: `prop:complete`, paper/paper.tex. Under the window condition and the side conditions, some
witness gives `κ̂ ≤ 7β/16 + 2^{-n}`.

The paper's proof has a probabilistic part and a deterministic part.
* The probabilistic part draws `𝒮` with rate `π_0` and the vectors `ξ` with the rates of the chain, and shows that
  the expected masked mass is at most `β/7` (paragraph *Masked mass*) and the expected uncertified
  fraction at most `β/4` (paragraph *Uncertified columns*). Some witness then has masked mass plus
  uncertified fraction at most `β/2` (`exists_witness_of_average`).
* The deterministic part bounds the radius of that witness (`radius_le`):
  `(Hi - Lo)/2 ≤ ½ Pr[mask = 0] + ½ (n_col - n_c)/n_col + (2M_F+1)η ≤ β/4 + 3β/16 = 7β/16`, and rounding adds at
  most `2^{-n}`.
-/

set_option autoImplicit false

namespace NearQuarticWires.Algorithm

open Finset
open NearQuarticWires.Sampler (Cell Frequency omega)

namespace CellCall

variable (C : CellCall)

/-- Proof of `prop:sound`, paper/paper.tex: `μ(z) = N^{-2} Σ_{u,v} mask(z,u,v)`. -/
noncomputable def columnMaskMean (z : Fin C.ncol) : ℝ :=
  (∑ u, ∑ v, C.realMask z (u, v)) / (C.seed.N : ℝ) ^ 2

/-- Proof of `prop:complete`, paper/paper.tex: the masked mass
`Pr_{z,u,v}[mask = 0] = n_col^{-1} Σ_z (1 - μ(z))`. -/
noncomputable def maskedMass : ℝ := (∑ z, (1 - C.columnMaskMean z)) / C.ncol

/-- Proof of `prop:complete`, paper/paper.tex: the uncertified fraction `(n_col - n_c)/n_col`. -/
noncomputable def uncertifiedFraction : ℝ := ((C.ncol : ℝ) - C.certifiedColumns.card) / C.ncol

/-- Every system on the seed path is solvable: on a certified column the function `H_{z,σ,δ}` solves it
(`prop:sound`, paper/paper.tex, "in particular it is consistent"). -/
theorem pathConsistent (H : C.ReconstructionHypotheses) : C.PathConsistent := by
  intro i hi b z hz σ hσ δ hδ
  have hlen : C.chosenSeed.length = C.seedLength := by
    unfold chosenSeed greedySeed
    have h : ∀ j : ℕ, ((greedyStep C.printedPotential)^[j] []).length = j := by
      intro j
      induction j with
      | zero => rfl
      | succ j ih =>
        rw [Function.iterate_succ_apply']
        simp [greedyStep, ih]
    exact h _
  have hπ : (C.chosenSeed.take i ++ [b]).length ≤ C.seedLength := by
    simp only [List.length_append, List.length_take, List.length_singleton, hlen]
    omega
  exact (C.reconstructedValue_eq H _ hπ z hz σ hσ δ hδ).1

theorem columnMaskMean_le_one (hN : 1 ≤ C.seed.N) (z : Fin C.ncol) : C.columnMaskMean z ≤ 1 := by
  have hN2 : (0 : ℝ) < (C.seed.N : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ C.seed.N := by exact_mod_cast hN
    positivity
  unfold columnMaskMean
  rw [div_le_one hN2]
  calc (∑ u, ∑ v, C.realMask z (u, v)) ≤ ∑ _u : Fin C.seed.N, ∑ _v : Fin C.seed.N, (1 : ℝ) :=
        Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => (abs_le.mp (C.realMask_abs_le z (u, v))).2
    _ = (C.seed.N : ℝ) ^ 2 := by simp [sq]

/-- Step 5, `prop:sound`, paper/paper.tex: rounding outward to multiples of `2^{-n}` adds at most
`2^{-n}` to the radius. -/
theorem centerRadius_radius_le (n : ℕ) (lo hi : ℚ) :
    (centerRadius n lo hi).2 ≤ (hi - lo) / 2 + 1 / 2 ^ n := by
  have hpos : (0 : ℚ) < 2 ^ n := by positivity
  have hf : lo - 1 / 2 ^ n ≤ dyadicFloor n lo := by
    unfold dyadicFloor
    rw [le_div_iff₀ hpos, sub_mul, one_div, inv_mul_cancel₀ hpos.ne']
    linarith [Int.sub_one_lt_floor (lo * 2 ^ n)]
  have hc : dyadicCeil n hi ≤ hi + 1 / 2 ^ n := by
    unfold dyadicCeil
    rw [div_le_iff₀ hpos, add_mul, one_div, inv_mul_cancel₀ hpos.ne']
    linarith [Int.ceil_lt_add_one (hi * 2 ^ n)]
  dsimp only [centerRadius]
  linarith

/-- **The deterministic part of `prop:complete`**, paper/paper.tex: if the masked mass plus the
uncertified fraction is at most `β/2`, `M_F ≥ 1` and `η = β/(16 M_F)`, then `κ̂ ≤ 7β/16 + 2^{-n}`. -/
theorem radius_le (F : C.FourierRows) (hB : C.SamplerBudget) (H : C.ReconstructionHypotheses) (β : ℚ)
    (hβ : 0 ≤ β) (hMF : 1 ≤ C.MF) (hη : C.η = β / (16 * C.MF)) (hcol : 0 < C.ncol)
    (hsum : C.maskedMass + C.uncertifiedFraction ≤ β / 2) :
    C.run.2 ≤ 7 * β / 16 + 1 / 2 ^ C.n := by
  classical
  have hN1 : 1 ≤ C.seed.N := le_trans (by norm_num) hB.two_le_N
  have hrun : C.run = centerRadius C.n (C.lower C.certifiedColumns C.samples)
      (C.upper C.certifiedColumns C.samples) := by
    unfold run
    rw [if_pos (C.pathConsistent H)]
  rw [hrun]
  refine (centerRadius_radius_le C.n _ _).trans ?_
  suffices h : ((C.upper C.certifiedColumns C.samples - C.lower C.certifiedColumns C.samples) / 2 : ℚ) ≤
      7 * β / 16 by linarith
  -- work over the reals
  have hμerr := (C.certified_errors_le F hB (C.potentialsExact H)).2
  set Z := C.certifiedColumns with hZ
  set S := C.samples with hS
  have hncol : (0 : ℝ) < C.ncol := by exact_mod_cast hcol
  have hMFr : (1 : ℝ) ≤ C.MF := by exact_mod_cast hMF
  have hηr : (C.η : ℝ) = β / (16 * C.MF) := by exact_mod_cast hη
  have hη0 : (0 : ℝ) ≤ C.η := by exact_mod_cast hB.eta_nonneg
  have hβr : (0 : ℝ) ≤ β := by exact_mod_cast hβ
  have hcard : (Z.card : ℝ) ≤ C.ncol := by
    have := Finset.card_le_univ Z
    simp only [Fintype.card_fin] at this
    exact_mod_cast this
  -- the mask errors: `Σ_{Z}(1 - μ̂) ≤ Σ_{Z}(1 - μ) + n_c η`
  have herr : ∀ z, Sampler.averagingError (C.realMask z) S = C.columnMaskMean z - C.sampledMask S z := by
    intro z
    rw [C.sampledMask_cast]
    rfl
  have hμhat : (∑ z ∈ Z, (1 - (C.sampledMask S z : ℝ))) ≤ (∑ z ∈ Z, (1 - C.columnMaskMean z)) + Z.card * C.η := by
    have : ∀ z ∈ Z, 1 - (C.sampledMask S z : ℝ) ≤ (1 - C.columnMaskMean z) +
        |Sampler.averagingError (C.realMask z) S| := by
      intro z _
      have h := le_abs_self (Sampler.averagingError (C.realMask z) S)
      rw [herr z] at h ⊢
      have h2 := neg_abs_le (C.columnMaskMean z - (C.sampledMask S z : ℝ))
      linarith
    have hs := Finset.sum_le_sum this
    rw [Finset.sum_add_distrib] at hs
    linarith
  -- the certified columns carry at most the whole masked mass
  have hsub : (∑ z ∈ Z, (1 - C.columnMaskMean z)) ≤ ∑ z, (1 - C.columnMaskMean z) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ Z)
      (fun z _ _ => by linarith [C.columnMaskMean_le_one hN1 z])
  have hsum' : (∑ z, (1 - C.columnMaskMean z)) + ((C.ncol : ℝ) - Z.card) ≤ (β / 2) * C.ncol := by
    have h := hsum
    unfold maskedMass uncertifiedFraction at h
    rw [← hZ, ← add_div, div_le_iff₀ hncol] at h
    exact_mod_cast h
  -- the radius
  have hdiff : ((C.upper Z S - C.lower Z S : ℚ) : ℝ) =
      ((∑ z ∈ Z, (1 - (C.sampledMask S z : ℝ))) + (4 * C.MF + 1) * Z.card * C.η +
        ((C.ncol : ℝ) - Z.card)) / C.ncol := by
    unfold upper lower
    push_cast
    rw [div_sub_div_same]
    congr 1
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    ring
  have hfinal : (((C.upper Z S - C.lower Z S) / 2 : ℚ) : ℝ) ≤ 7 * β / 16 := by
    push_cast
    rw [show ((C.upper Z S : ℝ) - C.lower Z S) = ((C.upper Z S - C.lower Z S : ℚ) : ℝ) by push_cast; ring,
      hdiff]
    rw [div_div, div_le_iff₀ (by positivity)]
    have hηMF : (2 * C.MF + 1 : ℝ) * C.η ≤ 3 * β / 16 := by
      rw [hηr]
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith
    have hc2 : (Z.card : ℝ) * C.η ≤ C.ncol * C.η := mul_le_mul_of_nonneg_right hcard hη0
    have hc3 : (2 * C.MF + 1 : ℝ) * (Z.card * C.η) ≤ (2 * C.MF + 1) * (C.ncol * C.η) :=
      mul_le_mul_of_nonneg_left hc2 (by positivity)
    nlinarith [hμhat, hsub, hsum', hηMF, hc3]
  exact_mod_cast hfinal

/-- Proof of `prop:complete`, paper/paper.tex: if the expected masked mass is at most `β/7` and the
expected uncertified fraction at most `β/4` under a probability distribution `P` on witnesses, some witness has
masked mass plus uncertified fraction at most `β/2`. -/
theorem exists_witness_of_average {Ω : Type} [Fintype Ω] (D : Ω → CellCall) (P : Ω → ℝ)
    (hP0 : ∀ ω, 0 ≤ P ω) (hP1 : ∑ ω, P ω = 1) (β : ℚ) (hβ : 0 ≤ β)
    (hmass : ∑ ω, P ω * (D ω).maskedMass ≤ β / 7)
    (hcert : ∑ ω, P ω * (D ω).uncertifiedFraction ≤ β / 4) :
    ∃ ω, (D ω).maskedMass + (D ω).uncertifiedFraction ≤ β / 2 := by
  by_contra hno
  push Not at hno
  have hβr : (0 : ℝ) ≤ β := by exact_mod_cast hβ
  have hlt : ∑ ω, P ω * ((β : ℝ) / 2) ≤ ∑ ω, P ω * ((D ω).maskedMass + (D ω).uncertifiedFraction) :=
    Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hno ω).le (hP0 ω)
  rw [← Finset.sum_mul, hP1, one_mul] at hlt
  simp only [mul_add, Finset.sum_add_distrib] at hlt
  -- equality is impossible unless `β = 0`; in that case use strictness of some term
  have hstrict : ∑ ω, P ω * ((β : ℝ) / 2) < ∑ ω, P ω * ((D ω).maskedMass + (D ω).uncertifiedFraction) := by
    obtain ⟨ω₀, hω₀⟩ : ∃ ω, 0 < P ω := by
      by_contra h
      push Not at h
      have : ∑ ω, P ω ≤ 0 := Finset.sum_nonpos fun ω _ => h ω
      linarith
    apply Finset.sum_lt_sum
    · exact fun ω _ => mul_le_mul_of_nonneg_left (hno ω).le (hP0 ω)
    · exact ⟨ω₀, Finset.mem_univ _, mul_lt_mul_of_pos_left (hno ω₀) hω₀⟩
  rw [← Finset.sum_mul, hP1, one_mul] at hstrict
  simp only [mul_add, Finset.sum_add_distrib] at hstrict
  linarith

/-- **`prop:complete`** (Existence of a useful witness), paper/paper.tex, for a family `D` of cell
calls indexed by the witnesses (the partition index of `lem:meanpop` fixed, and `𝒮`, `ξ` varying), under a
probability distribution `P` on the witnesses. The hypotheses `hmass` and `hcert` are the conclusions of the
paragraphs *Masked mass* (`prop:complete`: `lem:smaskmass`, `lem:meanpop`, `lem:filter`(a)) and *Uncertified
columns* (`prop:complete`: `lem:filter`(b,c), `lem:localize`, `lem:moments` and the window condition
`eq:window`); `hη` is the rule `η = β/(16 M_F)` of `sec:params` item 4. Then some witness gives
`κ̂ ≤ 7β/16 + 2^{-n}`. -/
theorem prop_complete {Ω : Type} [Fintype Ω] (D : Ω → CellCall) (P : Ω → ℝ)
    (hP0 : ∀ ω, 0 ≤ P ω) (hP1 : ∑ ω, P ω = 1) (n : ℕ) (hn : ∀ ω, (D ω).n = n) (β : ℚ) (hβ : 0 ≤ β)
    (F : ∀ ω, (D ω).FourierRows) (hB : ∀ ω, (D ω).SamplerBudget) (H : ∀ ω, (D ω).ReconstructionHypotheses)
    (hMF : ∀ ω, 1 ≤ (D ω).MF) (hη : ∀ ω, (D ω).η = β / (16 * (D ω).MF)) (hcol : ∀ ω, 0 < (D ω).ncol)
    (hmass : ∑ ω, P ω * (D ω).maskedMass ≤ β / 7)
    (hcert : ∑ ω, P ω * (D ω).uncertifiedFraction ≤ β / 4) :
    ∃ ω, (D ω).run.2 ≤ 7 * β / 16 + 1 / 2 ^ n := by
  obtain ⟨ω, hω⟩ := exists_witness_of_average D P hP0 hP1 β hβ hmass hcert
  refine ⟨ω, ?_⟩
  have h := (D ω).radius_le (F ω) (hB ω) (H ω) β hβ (hMF ω) (hη ω) (hcol ω) hω
  rwa [hn ω] at h

end CellCall

end NearQuarticWires.Algorithm
