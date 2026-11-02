import Proof.Quartic.Machine.GammaWork
import Proof.Wire_3_5.PrimAsmModulus
import Proof.Foundations.OrdinaryFramedSource

set_option autoImplicit false

namespace NearQuarticWires.StageGamma

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)

/-- `imp:seed` and `prop:time`, paper/paper.tex: the single field setup receives only the unary field degree. -/
def unaryFieldInput (request : Machine.GammaRequest) : List Bool :=
  List.replicate request.parameters.ell true

/-- `prop:time`, paper/paper.tex: the actual setup
clock includes physical input loading, bank creation and one field search. -/
def unaryFieldCost (request : Machine.GammaRequest) : ℕ :=
  4 * (unaryFieldInput request).length + 3 + PrimAsm.Modulus.modCost request.parameters.ell

/-- `imp:seed`, paper/paper.tex: one genuine cold
WordFunction builds its field-search bank from the unary degree and
computes the exact cached sampler modulus, with all other tapes blank. -/
noncomputable def unaryFieldWordFunction :
    WordFunction Machine.GammaRequest unaryFieldInput
      (fun request => frame (binary request.parameters.ell request.parameters.modulus)) unaryFieldCost :=
  FramedSource.ofRaw (by decide) PrimAsm.Modulus.modM 12 unaryFieldInput
    (fun request => frame (binary request.parameters.ell request.parameters.modulus))
    (fun request => PrimAsm.Modulus.modCost request.parameters.ell) (by
      intro request
      obtain ⟨A, ⟨r, hr, _, ht, _⟩, _, hout⟩ :=
        PrimAsm.Modulus.modulus_step request.parameters.ell request.parameters.one_le_ell
      refine ⟨r, ?_, ?_⟩
      · exact hr
      · rw [ht]
        exact hout)

/-- `prop:time`, paper/paper.tex: the one-time field
setup retains its explicit exponential factor and only polynomial loading. -/
theorem unaryFieldCost_le (request : Machine.GammaRequest) :
    unaryFieldCost request ≤
      1000 * (2 ^ (2 * request.parameters.ell) * (Cycle.seedLength request.parameters + 9)) := by
  have hs := Machine.gammaFieldSetupCost_le request
  have hell : request.parameters.ell ≤ Cycle.seedLength request.parameters := by
    dsimp [Cycle.seedLength]
    omega
  have hp : 1 ≤ 2 ^ (2 * request.parameters.ell) := Nat.one_le_two_pow
  have hq : Cycle.seedLength request.parameters + 9 ≤
      2 ^ (2 * request.parameters.ell) * (Cycle.seedLength request.parameters + 9) :=
    Nat.le_mul_of_pos_left _ (by positivity)
  dsimp [unaryFieldCost, unaryFieldInput, PrimAsm.Modulus.modCost]
  simp only [List.length_replicate]
  omega

end NearQuarticWires.StageGamma
