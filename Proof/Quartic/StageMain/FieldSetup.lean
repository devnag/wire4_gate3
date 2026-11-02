import Proof.Wire_3_5.PrimAsmModulus
import Proof.Foundations.OrdinaryFramedSource

/-!
# One-time field setup for the sampled main pass

Paper: `imp:seed`, paper/paper.tex, and `prop:time`. From the unary positive field degree, the ordinary
machine constructs its search workspace and computes the exact first
primitive modulus. The modulus is then available for all sample labels.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)

abbrev FieldRequest := {ell : ℕ // 1 ≤ ell}

def fieldUnaryWord (r : FieldRequest) : List Bool := List.replicate r.val true

def fieldModulusWord (r : FieldRequest) : List Bool := frame (binary r.val (GF.firstPrimitive r.val))

def fieldSetupCost (r : FieldRequest) : ℕ := 4 * (fieldUnaryWord r).length + 3 + PrimAsm.Modulus.modCost r.val

/-- A cold ordinary computation of the sampler modulus from its degree. -/
noncomputable def fieldSetupMachine :
    WordFunction FieldRequest fieldUnaryWord fieldModulusWord fieldSetupCost :=
  FramedSource.ofRaw (by decide) PrimAsm.Modulus.modM 12 fieldUnaryWord fieldModulusWord
    (fun r => PrimAsm.Modulus.modCost r.val) (by
      intro r
      obtain ⟨A, ⟨steps, run, _, bound, _⟩, _, output⟩ := PrimAsm.Modulus.modulus_step r.val r.property
      refine ⟨steps, run, ?_⟩
      rw [bound]
      exact output)

end NearQuarticWires.StageMain
