import Proof.Quartic.Program.Final
import Proof.Quartic.StageCertificateFinal.Final
import Proof.Quartic.StagePrintFinal.Final

/-!
# The counting theorem and the wire theorem, closed

`Program/Final.lean` assembles the counter from every stage except the certificate stage and the print subroutine,
which it takes as hypotheses. Both are now constructed: `StageCertificateFinal.certField` and
`StagePrintFinal.printField`, each from Williams' rectangular product (`Williams14_Corollary4_4`), the one published
input the counter's native tables use. Plugging them in gives `thm:counter` (`CounterExists4`) from that input, and the
wire theorem `FinalStatement4` from the transfer's inputs.
-/

set_option autoImplicit false

namespace NearQuarticWires.Program

open NearCubicWires

/-- The certificate stage, for every `B₁, B₂ > 0`. -/
theorem certField_nonempty (h : Bindings.Williams14.Williams14_Corollary4_4) :
    ∀ B1 B2 : ℕ, 0 < B1 → 0 < B2 → Nonempty (CertField B1 B2) :=
  fun B1 B2 h1 h2 => ⟨StageCertificateFinal.certField h B1 B2 h1 h2⟩

/-- The print subroutine, for every `B₁, B₂ > 0`. -/
theorem printField_nonempty (h : Bindings.Williams14.Williams14_Corollary4_4) :
    ∀ B1 B2 : ℕ, 0 < B1 → 0 < B2 → Nonempty (PrintField B1 B2) :=
  fun B1 B2 _ _ => ⟨StagePrintFinal.printField h B1 B2⟩

/-- **`thm:counter`** from Williams' rectangular product. -/
theorem counterExists4 (hW : Bindings.Williams14.Williams14_Corollary4_4) : Transfer.CounterExists4 :=
  counterExists4_of_stagesW hW certField_nonempty printField_nonempty

/-- **The wire theorem** (`thm:main`) from the inputs of the transfer. -/
theorem finalStatement4 (inputs : NearCubicGates.Close.NineInputs) : NearQuarticWires.Statement.FinalStatement4 :=
  finalStatement4_of_stagesW certField_nonempty printField_nonempty inputs

end NearQuarticWires.Program
