import Proof.Quartic.StageGamma.Enumeration

set_option autoImplicit false

namespace NearQuarticWires.StageGamma

open NearCubicGates.Close.Cells

/-- `cor:conditional`, paper/paper.tex: only literal
output operations alter the final scalar output stream; kernel input and
response operations have their own physically separate streams. -/
def outputsBits {V M : ℕ} : St V M → Bool
  | .op (.emit _) => true
  | .op _ => false
  | .seq s t => outputsBits s || outputsBits t
  | .ite _ s t => outputsBits s || outputsBits t
  | .loop _ s => outputsBits s

/-- `cor:conditional`, paper/paper.tex: a real
ordinary source execution with no final-output operations leaves that
stream unchanged, including all Gaussian calls and arithmetic loops. -/
theorem output_preserved {V M : ℕ} {C : Ctx} {s : St V M} {a b : DS V M} {n : ℕ}
    (h : Ex C s a b n) (hs : outputsBits s = false) : b.out = a.out := by
  induction h with
  | op h =>
    cases h <;> first | rfl | simp [outputsBits] at hs
  | seq h1 h2 ih1 ih2 =>
    simp only [outputsBits, Bool.or_eq_false_iff] at hs
    exact (ih2 hs.2).trans (ih1 hs.1)
  | iteT _ _ _ ih =>
    simp only [outputsBits, Bool.or_eq_false_iff] at hs
    exact ih hs.1
  | iteF _ _ _ ih =>
    simp only [outputsBits, Bool.or_eq_false_iff] at hs
    exact ih hs.2
  | loopF => rfl
  | loopT _ _ _ _ ih1 ih2 => exact (ih2 hs).trans (ih1 hs)
  | mono _ _ ih => exact ih hs

/-- `cor:conditional`, paper/paper.tex: all cache
decoding and static setup precede the final scalar output and preserve it. -/
theorem gammaPrelude_no_output : outputsBits gammaPrelude = false := by decide

end NearQuarticWires.StageGamma
