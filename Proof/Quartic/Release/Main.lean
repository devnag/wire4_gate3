import Proof.Quartic.Program.Final
import Proof.Quartic.Program.Closed
import Proof.Quartic.GateCorollary.Main
import Proof.Quartic.Statement.Release
import Proof.Quartic.Statement.JointChecks
import Proof.Quartic.GateCorollary.Budget
import SourceAdapters.Assembly

/-!
# The release theorem

Paper: `thm:main`, `thm:gates` and `thm:counter`, paper/paper.tex.

From the six published results of `NearCubicGates.Close.PublishedInputs` (through
`NearCubicGates.Adapters.sources_to_nine`), the stage `cert` of the counter program (Steps 1–2,
`Program.CertField`) and the printing subroutine (`Program.PrintField`), both built from Williams' rectangular
product (the field `rectangularProduct` of `NineInputs`), the joint theorem `JointStatement4` holds: `thm:main` by
`Program.finalStatement4_of_stagesW`, and `cor:gates` by `GateCorollary.jointStatement4_of_final`.
-/

set_option autoImplicit false

namespace NearQuarticWires.Release

open NearQuarticWires.Program

/-- **The release theorem with the stages `cert` and `print` as hypotheses** (`thm:main`, `thm:gates`); `main_from_published`
below discharges them. The stages `cert` and `print` are
built from Williams' rectangular product, which the published inputs supply (`rectangularProduct`). -/
theorem release_of_stages
    (hcert : NearCubicWires.Bindings.Williams14.Williams14_Corollary4_4 →
      ∀ B1 B2 : ℕ, 0 < B1 → 0 < B2 → Nonempty (CertField B1 B2))
    (hprint : NearCubicWires.Bindings.Williams14.Williams14_Corollary4_4 →
      ∀ B1 B2 : ℕ, 0 < B1 → 0 < B2 → Nonempty (PrintField B1 B2)) : ReleaseStatement :=
  fun h => GateCorollary.jointStatement4_of_final
    (finalStatement4_of_stagesW hcert hprint (NearCubicGates.Adapters.sources_to_nine h))

/-- **The release theorem** (`thm:main`, `thm:gates`): the six published results imply the joint statement. The
counter's two stages are built from Williams' rectangular product (`Program.finalStatement4`, `Program/Closed.lean`);
the gate corollary follows from the wire theorem (`GateCorollary.jointStatement4_of_final`). -/
theorem main_from_published : ReleaseStatement :=
  fun h => GateCorollary.jointStatement4_of_final
    (Program.finalStatement4 (NearCubicGates.Adapters.sources_to_nine h))

/-- **The near-cubic gate theorem in its published form**: the six published results imply
`NearCubicGates.Target.MainStatement`, whose cap is `⌊n^3/(K λ_n^{21/4} μ_n^7)⌋` (in the integer form `MainBudget`).
It follows from the charged top-weight half of `thm:gates` (paper/paper.tex) with the constant
`2K` in place of `K`, since `2K λ_n^{17/4} μ_n^{15/2} ≤ 2K λ_n^{21/4} μ_n^7` when `μ_n^{1/2} ≤ λ_n`
(`GateCorollary.mainStatement_of_gateStatement4`). -/
theorem gate_paper_main : NearCubicGates.Close.PublishedInputs → NearCubicGates.Target.MainStatement :=
  fun h => GateCorollary.mainStatement_of_gateStatement4 (Statement.jointStatement4_gates (main_from_published h))

end NearQuarticWires.Release

#print axioms NearQuarticWires.Release.release_of_stages
#print axioms NearQuarticWires.Release.main_from_published
