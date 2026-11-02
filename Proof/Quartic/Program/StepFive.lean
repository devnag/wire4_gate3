import Proof.Quartic.Program.Stages

/-!
# Step 5 from the data of the main pass

Paper: Step 5 of `sec:algorithm`, paper/paper.tex.

On a dispatched call, the value of the counter is a function of the data written by the stage `main`
(`Program.mainWord`): the input length `n`, the parameters `k`, `Q`, `M_F`, `η`, the number `n_c = |Z_c|` of
certified columns, path consistency, and the two totals `Σ_{Z_c} Q V̂` (`acceptTotal`) and `Σ_{Z_c} Q μ̂`
(`maskTotal`). With `n_col = 2^{n-k}`,

`Lo = n_col^{-1} [A/Q - 2 M_F n_c η]`, `Hi = n_col^{-1} [A/Q + n_c - M/Q + (2M_F+1) n_c η + (n_col - n_c)]`,

rounded outward to multiples of `2^{-n}` (`dispatched_value`). This is the exact specification of the arithmetic of
the stage `output`.
-/

set_option autoImplicit false

namespace NearQuarticWires.Program

open NearCubicGates.Close.Interfaces

/-- Step 5 of `sec:algorithm`: `Lo` from the total `A = Σ_{Z_c} Q V̂` and `n_c`. -/
noncomputable def stepFiveLower (n : ℕ) (p : Cells.Parameters) (A : ℤ) (nc : ℕ) : ℚ :=
  ((A : ℚ) / p.Q - 2 * p.MF * nc * p.eta) / (2 ^ (n - p.k) : ℕ)

/-- Step 5, `sec:analysis`: `Hi` from the totals `A = Σ_{Z_c} Q V̂`, `M = Σ_{Z_c} Q μ̂` and `n_c`. -/
noncomputable def stepFiveUpper (n : ℕ) (p : Cells.Parameters) (A M : ℤ) (nc : ℕ) : ℚ :=
  ((A : ℚ) / p.Q + nc - (M : ℚ) / p.Q + (2 * p.MF + 1) * nc * p.eta + (((2 ^ (n - p.k) : ℕ) : ℚ) - nc)) /
    (2 ^ (n - p.k) : ℕ)

theorem lower_eq_stepFive {c : Call} (p : Selected c) (w : List Bool) :
    (runCall c p w).lower (runCall c p w).certifiedColumns (runCall c p w).samples =
      stepFiveLower c.n p.1 (acceptTotal (runCall c p w)) (runCall c p w).certifiedColumns.card := by
  unfold Algorithm.CellCall.lower stepFiveLower acceptTotal Algorithm.CellCall.sampledAccept
  rw [← Finset.sum_div]
  simp only [Int.cast_sum, Int.cast_mul]
  rfl

theorem upper_eq_stepFive {c : Call} (p : Selected c) (w : List Bool) :
    (runCall c p w).upper (runCall c p w).certifiedColumns (runCall c p w).samples =
      stepFiveUpper c.n p.1 (acceptTotal (runCall c p w)) (maskTotal (runCall c p w))
        (runCall c p w).certifiedColumns.card := by
  unfold Algorithm.CellCall.upper stepFiveUpper acceptTotal maskTotal Algorithm.CellCall.sampledAccept
    Algorithm.CellCall.sampledMask
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div]
  simp only [Int.cast_sum, Int.cast_mul, Finset.sum_const, nsmul_eq_mul, mul_one]
  rfl

open Classical in
/-- **Step 5 on a dispatched call** (`sec:algorithm`, paper/paper.tex): the value of the counter is the sound default
if a system on the seed path is inconsistent, and otherwise the outward-rounded `(p̂, κ̂)` of `stepFiveLower`,
`stepFiveUpper` at the totals of the main pass. -/
theorem dispatched_value {B1 B2 : ℕ} {c : Call} {p : Selected c} (hd : dispatch B1 B2 c = some p)
    (w : List Bool) :
    admittedValue B1 B2 Builder.value c w =
      if (runCall c p w).PathConsistent then
        Algorithm.centerRadius c.n
          (stepFiveLower c.n p.1 (acceptTotal (runCall c p w)) (runCall c p w).certifiedColumns.card)
          (stepFiveUpper c.n p.1 (acceptTotal (runCall c p w)) (maskTotal (runCall c p w))
            (runCall c p w).certifiedColumns.card)
      else Algorithm.soundDefault := by
  obtain ⟨hadm, hW⟩ := dispatch_admitted hd
  rw [admittedValue_of_admitted _ hadm, Builder.value_eq_run c (Builder.Shaped.of_admitted hadm) hW p.2 w]
  rw [← lower_eq_stepFive p w, ← upper_eq_stepFive p w]
  unfold Algorithm.CellCall.run
  rfl

end NearQuarticWires.Program
