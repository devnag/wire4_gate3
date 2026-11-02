import Proof.Quartic.StagePrep.WordCases
import Proof.Gates.Dispatch.Zero

/-!
# The exact constant-call value and duplicate parity indices

Paper: `sec:params`, paper/paper.tex.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Interfaces
open NearCubicGates.Close.Dispatch

/-- The parity test of `sec:params`, paper/paper.tex, is equivalent on the original range and the encoded
index list, including repeated indices. -/
theorem odd_count_range_iff (c : Call) (hall : ∀ i ∈ c.parity, i < c.n) :
    (∃ i ∈ Finset.range c.n, c.parity.count i % 2 = 1) ↔
      ∃ i ∈ c.parity, c.parity.count i % 2 = 1 := by
  constructor
  · rintro ⟨i, _, hi⟩
    exact ⟨i, List.count_pos_iff.1 (by omega), hi⟩
  · rintro ⟨i, hi, hodd⟩
    exact ⟨i, Finset.mem_range.2 (hall i hi), hodd⟩

/-- The exact closed value of `sec:params`, paper/paper.tex, agrees with the physical constant-call selector. -/
theorem closedValue_eq_zval (c : Call) (hall : ∀ i ∈ c.parity, i < c.n) :
    Builder.closedValue c = (zval c, 0) := by
  unfold Builder.closedValue zval
  cases c.kind with
  | single => rfl
  | pair => rfl
  | parity =>
    have hi : (∃ i < c.n, c.parity.count i % 2 = 1) ↔
        ∃ i ∈ c.parity, c.parity.count i % 2 = 1 := by
      simpa only [Finset.mem_range] using odd_count_range_iff c hall
    by_cases h : ∃ i ∈ c.parity, c.parity.count i % 2 = 1
    · have hr : ∃ i < c.n, c.parity.count i % 2 = 1 := hi.2 h
      simp [Builder.oddParity, hr, h]
    · have hr : ¬ ∃ i < c.n, c.parity.count i % 2 = 1 := fun h' => h (hi.1 h')
      simp [Builder.oddParity, hr, h, Builder.bitQ, Builder.constantValue]

end NearQuarticWires.StagePrep
