import Proof.Quartic.Algorithm.Complete
import Proof.Quartic.Machine.StepSemantics

/-!
# The seed-fixing objective is an integer

Paper: Step 3 of `sec:algorithm`, paper/paper.tex, and step (1) of the proof of `prop:sound`.

On a certified column, the exact system of Step 3 has the unique solution `H_{z,σ,δ}` (by `imp:window`), whose
value at `0` is a sum of the integer walk weights `2^S c_π(w)` (`cor:conditional`). The weights `κ_σ` are integers
(`lem:cycle`). Hence every value of the objective `Ψ̃(π)` met by the algorithm (prefixes of length at most `S`) is
the integer `printedPotentialInt π`, and the greedy seed of the algorithm is the seed chosen by the integer-valued
greedy loop `Machine.chosenSeed` (`chosenSeed_eq_machine`).
-/

set_option autoImplicit false

namespace NearQuarticWires.Builder

open Finset

section Integer

variable (C : Algorithm.CellCall)

/-- Step 3, `sec:algorithm`, paper/paper.tex: the integer
`H_{z,σ,δ}(0) = Σ_{w : mask_w(z) = 1, E(w) = δ, Y(w) = 0} 2^S c_π(w)`. -/
noncomputable def classValueInt (π : List Bool) (z : Fin C.ncol) (σ : Cycle.SignPattern Algorithm.traceOrder)
    (δ : Fin 2 → Fin (C.J + 1) → ℤ) : ℤ := by
  classical
  exact ∑ w, if C.walkMask z w = 1 ∧ C.HasDigits z σ w δ ∧ C.walkSums z σ w = 0 then C.walkWeight π w else 0

/-- Step 3, `sec:algorithm`, paper/paper.tex: the integer objective
`Σ_{z ∈ Z_c} Σ_σ κ_σ Σ_δ H_{z,σ,δ}(0)`. -/
noncomputable def printedPotentialInt (π : List Bool) : ℤ :=
  ∑ z ∈ C.certifiedColumns, ∑ σ : Cycle.SignPattern Algorithm.traceOrder,
    Cycle.kappa Algorithm.traceOrder σ * ∑ δ ∈ C.digitVectors z, classValueInt C π z σ δ

/-- The rational class function at `0` is the integer `classValueInt`. -/
theorem classFunction_zero (π : List Bool) (z : Fin C.ncol) (σ : Cycle.SignPattern Algorithm.traceOrder)
    (δ : Fin 2 → Fin (C.J + 1) → ℤ) : C.classFunction π z σ δ 0 = (classValueInt C π z σ δ : ℚ) := by
  classical
  unfold Algorithm.CellCall.classFunction classValueInt
  push_cast
  refine Finset.sum_congr rfl fun w _ => ?_
  split_ifs <;> simp

/-- **The objective of Step 3 is an integer** (`sec:algorithm`, paper/paper.tex): at every prefix of
length at most `S`, `Ψ̃(π) = printedPotentialInt π`. -/
theorem printedPotential_int (H : C.ReconstructionHypotheses) (π : List Bool) (hπ : π.length ≤ C.seedLength) :
    C.printedPotential π = (printedPotentialInt C π : ℚ) := by
  classical
  unfold Algorithm.CellCall.printedPotential printedPotentialInt
  push_cast
  refine Finset.sum_congr rfl fun z hz => Finset.sum_congr rfl fun σ _ => ?_
  by_cases hσ : Cycle.kappa Algorithm.traceOrder σ = 0
  · simp [hσ]
  · congr 1
    refine Finset.sum_congr rfl fun δ hδ => ?_
    rw [(C.reconstructedValue_eq H π hπ z hz σ hσ δ hδ).2, classFunction_zero]

/-- The greedy seed of Step 3 depends only on the objective at prefixes of length at most `S`; if these values are
the integers `R`, it is the seed of the integer-valued greedy loop `Machine.chosenSeed`. -/
theorem greedySeed_eq_machine (S : ℕ) (Ψ : List Bool → ℚ) (R : List Bool → ℤ)
    (hR : ∀ π : List Bool, π.length ≤ S → Ψ π = (R π : ℚ)) :
    Algorithm.greedySeed S Ψ = Machine.chosenSeed S R := by
  unfold Algorithm.greedySeed Machine.chosenSeed NearCubicWires.WireExponent3_5.SeedFix.greedyLoop
  have key : ∀ i, i ≤ S → (Algorithm.greedyStep Ψ)^[i] [] =
      (NearCubicWires.WireExponent3_5.SeedFix.greedyStep R)^[i] [] ∧
      ((Algorithm.greedyStep Ψ)^[i] []).length = i := by
    intro i
    induction i with
    | zero => intro _; exact ⟨rfl, rfl⟩
    | succ i ih =>
      intro hi
      obtain ⟨heq, hlen⟩ := ih (by omega)
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', heq]
      set q := (NearCubicWires.WireExponent3_5.SeedFix.greedyStep R)^[i] []
      have hq : q.length = i := heq ▸ hlen
      have ht : Ψ (q ++ [true]) = (R (q ++ [true]) : ℚ) := hR _ (by simp [hq]; omega)
      have hf : Ψ (q ++ [false]) = (R (q ++ [false]) : ℚ) := hR _ (by simp [hq]; omega)
      refine ⟨?_, ?_⟩
      · unfold Algorithm.greedyStep NearCubicWires.WireExponent3_5.SeedFix.greedyStep
        rw [ht, hf]
        simp only [Int.cast_lt]
      · unfold Algorithm.greedyStep
        simp [hq]
  exact (key S le_rfl).1

/-- **The dock of Step 3 to the machine**: under the reconstruction hypotheses, the seed chosen by the algorithm is
`Machine.chosenSeed S (printedPotentialInt C)`, the integer-valued greedy loop on the integer objective. -/
theorem chosenSeed_eq_machine (H : C.ReconstructionHypotheses) :
    C.chosenSeed = Machine.chosenSeed C.seedLength (printedPotentialInt C) :=
  greedySeed_eq_machine C.seedLength C.printedPotential (printedPotentialInt C)
    (fun π hπ => printedPotential_int C H π hπ)

end Integer

end NearQuarticWires.Builder
