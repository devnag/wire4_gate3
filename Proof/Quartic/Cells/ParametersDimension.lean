import Proof.Quartic.Cells.ParametersStars
import Proof.Quartic.Cycle.Basic

set_option autoImplicit false

namespace NearQuarticWires.Cells.CoreRules

variable {x : ParameterInput} {p : Parameters}

/-- `sec:params`, paper/paper.tex: the actual selected
inner dimension is even. -/
theorem k_even (hs : CoreRules x p) : Even p.k := by
  obtain ⟨r, hr⟩ := hs.r_even_large.1
  refine ⟨r * p.s, ?_⟩
  rw [hs.k_eq, hr]
  ring

/-- `sec:params`, paper/paper.tex: the selected matrix
side satisfies the exact power identity `N² = 2^k`. -/
theorem N_square (hs : CoreRules x p) : p.N ^ 2 = 2 ^ p.k := by
  rw [hs.N_eq, ← pow_mul, Nat.div_mul_cancel (even_iff_two_dvd.mp hs.k_even)]

/-- `imp:partition` and `sec:params`, paper/paper.tex: one side of a cell has exactly the selected matrix dimension. -/
theorem errors_card (hs : CoreRules x p) : Fintype.card hs.starParams.Errors = p.N := by
  have hk : p.s * (p.r / 2) = p.k / 2 := by
    calc
      p.s * (p.r / 2) = (p.s * p.r) / 2 :=
        (Nat.mul_div_assoc p.s (even_iff_two_dvd.mp hs.r_even_large.1)).symm
      _ = (p.r * p.s) / 2 := by rw [Nat.mul_comm p.s p.r]
      _ = p.k / 2 := by rw [hs.k_eq]
  change Fintype.card (Fin (p.r / 2) → Option (Fin hs.starParams.b)) = p.N
  rw [Fintype.card_fun, hs.starParams.card_option_b, Fintype.card_fin, hs.star_s,
    ← pow_mul, hk, hs.N_eq]

/-- `lem:cycle` and `sec:algorithm`, paper/paper.tex: the actual closed-walk type has the printed `2^(mk)` census. -/
theorem walks_card (hs : CoreRules x p) :
    Fintype.card (Cycle.Walk p.N p.m) = 2 ^ (p.m * p.k) := by
  calc
    Fintype.card (Cycle.Walk p.N p.m) = p.N ^ (2 * p.m) := by
      simp only [Cycle.Walk, Fintype.card_fun, Fintype.card_fin]
    _ = (p.N ^ 2) ^ p.m := pow_mul _ _ _
    _ = (2 ^ p.k) ^ p.m := by rw [hs.N_square]
    _ = 2 ^ (p.m * p.k) := by rw [← pow_mul]; congr 1; ring

end NearQuarticWires.Cells.CoreRules

namespace NearQuarticWires.Cells.ParameterRules

variable {x : ParameterInput} {p : Parameters}

/-- `sec:params`, paper/paper.tex: the actual selected
inner dimension is even. -/
theorem k_even (hs : ParameterRules x p) : Even p.k :=
  CoreRules.k_even (hs : CoreRules x p)

/-- `sec:params`, paper/paper.tex: the selected matrix
side satisfies the exact power identity `N² = 2^k`. -/
theorem N_square (hs : ParameterRules x p) : p.N ^ 2 = 2 ^ p.k :=
  CoreRules.N_square (hs : CoreRules x p)

/-- `imp:partition` and `sec:params`, paper/paper.tex: one side of a cell has exactly the selected matrix dimension. -/
theorem errors_card (hs : ParameterRules x p) : Fintype.card hs.starParams.Errors = p.N :=
  CoreRules.errors_card (hs : CoreRules x p)

/-- `lem:cycle` and `sec:algorithm`, paper/paper.tex: the actual closed-walk type has the printed `2^(mk)` census. -/
theorem walks_card (hs : ParameterRules x p) :
    Fintype.card (Cycle.Walk p.N p.m) = 2 ^ (p.m * p.k) :=
  CoreRules.walks_card (hs : CoreRules x p)

end NearQuarticWires.Cells.ParameterRules

