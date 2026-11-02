import Proof.Quartic.Builder.Draws
import Proof.Quartic.Builder.Bernstein
import Proof.Quartic.Cells.ParametersBuilderCap

/-!
# The mathematical half of `thm:counter`, from the statement's inputs

Paper: `thm:counter` (Theorem 4.1), paper/paper.tex, items (i) and (ii), and its proof.

`counterMath4 B1 B2` is the counting algorithm `Builder.value` with soundness for every call and witness and
completeness under the cap `W ≤ a β 𝒜₄(n)`, with no published input: the cap of `lem:asymptotics` is
`Cells.builder_quarticCap`, and the finite Bernstein inequality used by `lem:localize` (`localizeLaw_drawLaw`) is
proved (`vershynin18_finiteBernstein`). `counterMath4_of_bernstein` takes the Bernstein inequality as a parameter.
-/

set_option autoImplicit false

namespace NearQuarticWires.Builder

/-- `thm:counter`(i),(ii) (paper/paper.tex) for the counting algorithm `Builder.value`, from the
finite Bernstein inequality. -/
noncomputable def counterMath4_of_bernstein
    (bernstein : NearCubicGates.PublishedSources.Witness.Vershynin18_Theorem2_8_4_FiniteBernstein.{0, 0})
    (B1 B2 : ℕ) : CounterMath4 B1 B2 :=
  counterMath4_of_localize (Cells.builder_quarticCap B1 B2) fun c p hs _ _ =>
    ⟨drawLaw c p, drawLaw_nonneg c p, sum_drawLaw hs, localizeLaw_drawLaw c hs bernstein⟩

/-- **`thm:counter`(i),(ii)** (paper/paper.tex) for the counting algorithm `Builder.value`, with no
published input. -/
noncomputable def counterMath4 (B1 B2 : ℕ) : CounterMath4 B1 B2 :=
  counterMath4_of_bernstein vershynin18_finiteBernstein B1 B2

/-- The value function of `counterMath4` is the counting algorithm `Builder.value`. -/
theorem counterMath4_value (B1 B2 : ℕ) : (counterMath4 B1 B2).value = value := rfl

end NearQuarticWires.Builder
