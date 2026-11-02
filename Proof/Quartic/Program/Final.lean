import Proof.Quartic.Greedy.Main
import Proof.Quartic.Control.SeedLoop
import Proof.Quartic.Control.GammaTable
import Proof.Quartic.Reconstruct.Final
import Proof.Quartic.StagePrep.Final
import Proof.Quartic.StageOutput.Final
import Proof.Quartic.StageMainMask.Final
import Proof.Quartic.StageGamma.Final
import Proof.Gates.Solve.Machine
import Proof.Quartic.Builder.Counter

/-!
# `thm:main` from the stages `cert` and `print`

Paper: `thm:main`, paper/paper.tex; `thm:counter`; `sec:algorithm`;
`prop:time`.

The counter program is assembled from its proved stages: parameter preparation (`StagePrep.prep`), Step 4
(`StageMainMask.main`), Step 5 (`StageOutput.output`), and Step 3 (`greedy`) from the control of the `S` rounds
(`Control.seedLoop`), the coefficient stage (`Control.gammaTableControl`), the reconstruction
(`Reconstruct.reconstructControl`) and its subroutines: one coefficient (`StageGamma.gammaWordFunction`), the exact
solver (`Solve.solveMachine`) and one printed table. This file takes two stages as hypotheses, each of exactly the type of
its field: Steps 1–2 (`CertField`, the field `cert` of `MachineComponents` with its cost) and one printed table
(`PrintField`, the field `print` of `Greedy.SubroutineCosts` with its cost). `counterExists4_of_stages` and
`finalStatement4_of_stages` derive `CounterExists4` and the statement from them; `Program/Closed.lean` builds both stages
from Williams' rectangular product.
-/

set_option autoImplicit false

namespace NearQuarticWires.Program

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces
open NearQuarticWires.Greedy

/-- **The stage `cert`** (Steps 1–2, `sec:algorithm`, paper/paper.tex): the fields `certBudget`, `cert` and
`certCost` of `MachineComponents`. -/
structure CertField (B1 B2 : ℕ) where
  /-- The cost of `cert`. -/
  certBudget : Call → List Bool → ℕ
  /-- Steps 1–2: incidences, structural mask, walk list, certification tables and `Z_c`. -/
  cert : WordFunction (Call × List Bool) (fun r => prepWord B1 B2 r.1 r.2)
    (fun r => frame (certWord B1 B2 r.1 r.2)) (fun r => certBudget r.1 r.2)
  certCost : LedgerCost B1 B2 certBudget

/-- **The open subroutine `print`** (`lem:print`(a), `lem:residue`; `prop:time`): the fields
`printBudget`, `print`, `Kp`, `ep` and `printCost` of `Greedy.SubroutineCosts`. -/
structure PrintField (B1 B2 : ℕ) where
  /-- The cost of one table. -/
  printBudget : PrintRequest B1 B2 → ℕ
  /-- One table of recovered counts `z ↦ 𝒩(z)`. -/
  print : WordFunction (PrintRequest B1 B2) printInput
    (fun r => listWord NearCubicGates.Close.Interfaces.intWord (printTable r)) printBudget
  /-- The constant of the cost of one table. -/
  Kp : ℕ
  /-- The exponent of the cost of one table. -/
  ep : ℕ
  /-- One printed table costs `2^{n-k} poly(n)`, plus a polynomial in the size of its indices. -/
  printCost : ∀ r : PrintRequest B1 B2,
    printBudget r ≤ Kp * (2 ^ (r.child.call.n - r.child.selected.1.k) * (r.child.call.n + 1) ^ ep +
      ((printIndexWord r).length + 1) ^ ep)

variable {B1 B2 : ℕ}

/-- The subroutines of a child evaluation: the proved coefficient machine and exact solver, and a printed table. -/
noncomputable def subroutinesOf (P : PrintField B1 B2) : SubroutineCosts B1 B2 where
  gammaBudget := StageGamma.gammaBudget
  gamma := StageGamma.gammaWordFunction
  Kγ := StageGamma.gammaCostConstant B1 B2
  eγ := StageGamma.gammaCostExponent B1 B2
  gammaCost := fun q w => StageGamma.gammaCost q w
  printBudget := P.printBudget
  print := P.print
  Kp := P.Kp
  ep := P.ep
  printCost := P.printCost
  solver := NearCubicGates.Close.Solve.solveMachine

/-- **The parts of the stage `greedy`** (Step 3 of `sec:algorithm`). -/
noncomputable def greedyPartsOf (P : PrintField B1 B2) : GreedyParts B1 B2 where
  loop := Control.seedLoop B1 B2
  gammaTable := Control.gammaTableControl B1 B2
  reconstruct := Reconstruct.reconstructControl B1 B2
  subroutines := subroutinesOf P

/-- **The stages other than `greedy`**: the proved `prep`, `main` and `output`, and the stage `cert`. -/
noncomputable def otherStagesOf (Cf : CertField B1 B2) : OtherStages B1 B2 where
  prepBudget := StagePrep.prepBudget B1 B2
  prep := StagePrep.prep B1 B2
  prepCost := StagePrep.prepCost B1 B2
  certBudget := Cf.certBudget
  cert := Cf.cert
  certCost := Cf.certCost
  mainBudget := StageMainMask.mainBudget B1 B2
  main := StageMainMask.main B1 B2
  mainCost := StageMainMask.mainCost B1 B2
  outputBudget := StageOutput.outputBudget B1 B2
  output := StageOutput.output B1 B2
  outputCost := StageOutput.outputCost B1 B2

/-- **The machine components of the counter** from the stage `cert` and the subroutine `print`. -/
noncomputable def machineComponentsOf (Cf : CertField B1 B2) (P : PrintField B1 B2) : MachineComponents B1 B2 :=
  (otherStagesOf Cf).withGreedy (greedyPartsOf P)

/-- **`CounterExists4` from the stages `cert` and `print`** (`thm:counter`), with the mathematical half
`Builder.counterMath4`. -/
theorem counterExists4_of_stages (hcert : ∀ B1 B2 : ℕ, 0 < B1 → 0 < B2 → Nonempty (CertField B1 B2))
    (hprint : ∀ B1 B2 : ℕ, 0 < B1 → 0 < B2 → Nonempty (PrintField B1 B2)) : Transfer.CounterExists4 :=
  counterExists4_of_components (fun B1 B2 _ _ => ⟨Builder.counterMath4 B1 B2, Builder.counterMath4_value B1 B2⟩)
    fun B1 B2 h1 h2 =>
      let ⟨Cf⟩ := hcert B1 B2 h1 h2
      let ⟨P⟩ := hprint B1 B2 h1 h2
      ⟨machineComponentsOf Cf P⟩

/-- **`thm:main` from the stages `cert` and `print` and the eight intermediate inputs (`NineInputs`)** (via `Transfer.transfer4_official`). -/
theorem finalStatement4_of_stages (hcert : ∀ B1 B2 : ℕ, 0 < B1 → 0 < B2 → Nonempty (CertField B1 B2))
    (hprint : ∀ B1 B2 : ℕ, 0 < B1 → 0 < B2 → Nonempty (PrintField B1 B2))
    (inputs : NearCubicGates.Close.NineInputs) : NearQuarticWires.Statement.FinalStatement4 :=
  Transfer.transfer4_official inputs (counterExists4_of_stages hcert hprint)

/-! ## The stages from Williams' rectangular product

The table backends of `cert` and `print` use Williams' rectangular matrix product (`Williams14_Corollary4_4`, a
published input, the field `rectangularProduct` of `NineInputs`). -/

/-- **`CounterExists4` from Williams' rectangular product and the two stages built from it.** -/
theorem counterExists4_of_stagesW (hW : NearCubicWires.Bindings.Williams14.Williams14_Corollary4_4)
    (hcert : NearCubicWires.Bindings.Williams14.Williams14_Corollary4_4 →
      ∀ B1 B2 : ℕ, 0 < B1 → 0 < B2 → Nonempty (CertField B1 B2))
    (hprint : NearCubicWires.Bindings.Williams14.Williams14_Corollary4_4 →
      ∀ B1 B2 : ℕ, 0 < B1 → 0 < B2 → Nonempty (PrintField B1 B2)) : Transfer.CounterExists4 :=
  counterExists4_of_stages (hcert hW) (hprint hW)

/-- **`thm:main` from the eight intermediate inputs (`NineInputs`) and the two stages built from Williams' product.** -/
theorem finalStatement4_of_stagesW
    (hcert : NearCubicWires.Bindings.Williams14.Williams14_Corollary4_4 →
      ∀ B1 B2 : ℕ, 0 < B1 → 0 < B2 → Nonempty (CertField B1 B2))
    (hprint : NearCubicWires.Bindings.Williams14.Williams14_Corollary4_4 →
      ∀ B1 B2 : ℕ, 0 < B1 → 0 < B2 → Nonempty (PrintField B1 B2))
    (inputs : NearCubicGates.Close.NineInputs) : NearQuarticWires.Statement.FinalStatement4 :=
  Transfer.transfer4_official inputs (counterExists4_of_stagesW inputs.rectangularProduct hcert hprint)

end NearQuarticWires.Program
