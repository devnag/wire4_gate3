import Proof.Quartic.StageCert.Records

set_option autoImplicit false

namespace NearQuarticWires.StageCertTests

/-- `sec:cycle`, paper/paper.tex:
the sign pattern at one literal eight-bit ordinal. -/
def patternOfCode (code : ℕ) : Cycle.SignPattern 4 := fun i => code.testBit i.val

/-- `sec:cycle`, paper/paper.tex:
the exact number of true bits consumed by a fixed low-bit scan. -/
def lowerBitSum : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n+1, code => code%2 + lowerBitSum n (code/2)

/-- `sec:cycle`, paper/paper.tex:
at most one true bit is added for each scanned position. -/
theorem lowerBitSum_le (n code : ℕ) : lowerBitSum n code ≤ n := by
  induction n generalizing code with
  | zero => rfl
  | succ n ih =>
    have hm := Nat.mod_lt code (by decide : 0<2)
    have hh := ih (code/2)
    simp only [lowerBitSum]
    omega

/-- `lem:cycle`, paper/paper.tex:
the exact nonzero-κ classifier is even parity of the eight literal
sign bits, in the same ordinal order as the complete sign enumeration. -/
theorem kappa_patternOfCode (code : Fin 256) :
    (decide (Cycle.kappa 4 (patternOfCode code.val) ≠ 0)) =
      decide (lowerBitSum 8 code.val % 2 = 0) := by
  decide +kernel +revert

end NearQuarticWires.StageCertTests
