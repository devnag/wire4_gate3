import Proof.Quartic.Transfer.CaseOne4
import Proof.Quartic.Worker.Recovery.AfterFinal
import Proof.Quartic.Worker.Setup.CompU
import Proof.Gates.Main.Application
import Proof.Gates.Recovery.Common
import Proof.Gates.ENP.TableStage
import Proof.Gates.Succinct.Main
import Proof.Gates.Succinct.SubstitutionReady

/-!
# The main theorem from the wire-measured closure (paper `prop:ae-final`)

Every wire-measured closure gives a native frontier (`frontier4_of_closure4`): the schedule, Case 1, Case 2 and the
`E^NP` recovery. Hence the main theorem follows from `ClosureSupply4`, a closure at every `0 < ε < γ/5`
(`final4_of_closureSupply4`). The recovery of the padded native family is the near-cubic gate proof's
(`Proof.Gates.Recovery.Common`), with its after-refuter supply taken from the weak machine's set-up of the wire measure
(`NearQuarticWires.Worker4.Recovery.afterSupply_of`): it uses the source circuit, the oracle and the proof-oracle
circuit, and no target circuit.
-/

set_option autoImplicit false

namespace NearQuarticWires.Transfer

open NearCubicWires NearCubicGates.Close NearCubicGates.Close.Transfer NearCubicGates.Close.Gadget

variable {s : GateSources} {P : ThreeQueryPCPP} {ε : ℝ}

/-- The closure with the source onset of its parameters raised to `o`. -/
noncomputable def GateClosure4.withOnset (c : GateClosure4 s P ε) (o : ℕ) : GateClosure4 s P ε where
  base := Transfer.withOnset c.base o
  wbudget := c.wbudget
  wLower := c.wLower
  wUpper := c.wUpper
  wcomplete := c.wcomplete

/-- The recovery of the padded native family. -/
theorem recoverySupply : RecoverySupply :=
  Recovery.Common.recoverySupply_of
    (NearQuarticWires.Worker4.Recovery.afterSupply_of ENP.tStageRuns
      (NearQuarticWires.Worker4.Setup.compU_of Succinct.SubstMachine.substReady))

/-- Every wire-measured closure gives a native frontier. -/
theorem frontier4_of_closure4 (c : GateClosure4 s P ε) (hε : 0 < ε) :
    Nonempty (NativeFrontier4 (P.gamma : ℝ) ε) := by
  obtain ⟨o, _, hrec⟩ := recoverySupply s P ε c.base
  let c' := c.withOnset o
  exact frontier4_of_parts c'.base c'.wbudget (schedulePart4 c'.base c'.wbudget c'.wLower)
    (caseOnePart4 c'.base hε c'.wbudget c'.wUpper) (caseTwoPart4 c') hrec

/-- A wire-measured closure at every admissible `ε`. -/
def ClosureSupply4 : Prop :=
  ∀ (s : GateSources) (P : ThreeQueryPCPP) (ε : ℝ), 0 < ε → ε < (P.gamma : ℝ) / 5 → Nonempty (GateClosure4 s P ε)

/-- **The main theorem from the wire-measured closures.** -/
theorem final4_of_closureSupply4 (h : ClosureSupply4) : FinalStatement4' := by
  intro inputs
  have s := gateSources_of_inputs inputs (fun _k H G => Succinct.succinctVerifier_exists H G)
  obtain ⟨P⟩ := threeQuery_of_source s.threeQueryPCPP
  exact mainStatement4_of_native_frontier4 P.gamma P.gamma_pos P.gamma_lt_one fun ε hε hεγ => by
    obtain ⟨c⟩ := h s P ε hε hεγ
    exact frontier4_of_closure4 c hε

end NearQuarticWires.Transfer
