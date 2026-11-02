import Proof.Quartic.StageMain.FieldExtractMachine
import Proof.Quartic.StageMain.FieldSetup
import Proof.Quartic.StageGamma.Retain

/-!
# One computed field cache for the whole main pass

`imp:seed`, paper/paper.tex, and `prop:time`: the degree is read from the original source and its primitive
modulus is computed once. A paid retained-input composition appends its
fixed-width binary cache while preserving the original certificate and seed.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5
open NearCubicGates.Close.Interfaces

noncomputable def mainFieldRequest (B1 B2 : ℕ) (c : Call) : FieldRequest :=
  ⟨mainFieldDegree B1 B2 c, mainFieldDegree_pos B1 B2 c⟩

noncomputable def mainFieldBits (B1 B2 : ℕ) (c : Call) : List Bool :=
  binary (mainFieldDegree B1 B2 c) (GF.firstPrimitive (mainFieldDegree B1 B2 c))

noncomputable def mainFieldCost (B1 B2 : ℕ) (c : Call) (w : List Bool) : ℕ :=
  4 * fieldExtractCost B1 B2 c w + 4 * fieldSetupCost (mainFieldRequest B1 B2 c) + 12

noncomputable def mainFieldWordFunction (B1 B2 : ℕ) :
    WordFunction (Call × List Bool) (fun r => Program.greedyWord B1 B2 r.1 r.2)
      (fun r => frame (mainFieldBits B1 B2 r.1)) (fun r => mainFieldCost B1 B2 r.1 r.2) := by
  let setup : WordFunction (Call × List Bool)
      (fun r => List.replicate (mainFieldDegree B1 B2 r.1) true)
      (fun r => frame (mainFieldBits B1 B2 r.1))
      (fun r => fieldSetupCost (mainFieldRequest B1 B2 r.1)) :=
    ⟨fieldSetupMachine.program, fun r => fieldSetupMachine.realizes (mainFieldRequest B1 B2 r.1)⟩
  exact Program.WordFunction.pipe (fieldExtractWordFunction B1 B2) setup

noncomputable def cachedMainWord (B1 B2 : ℕ) (c : Call) (w : List Bool) : List Bool :=
  Program.greedyWord B1 B2 c w ++ mainFieldBits B1 B2 c

noncomputable def retainedMainFieldCost (B1 B2 : ℕ) (c : Call) (w : List Bool) : ℕ :=
  2 * (2 * mainFieldCost B1 B2 c w +
    150 * ((Program.greedyWord B1 B2 c w).length + (mainFieldBits B1 B2 c).length + 1)) + 2

noncomputable def retainedMainFieldWordFunction (B1 B2 : ℕ) :
    WordFunction (Call × List Bool) (fun r => Program.greedyWord B1 B2 r.1 r.2)
      (fun r => frame (cachedMainWord B1 B2 r.1 r.2))
      (fun r => retainedMainFieldCost B1 B2 r.1 r.2) := by
  unfold cachedMainWord retainedMainFieldCost
  exact StageGamma.retainedWordFunction
    (input := fun r : Call × List Bool => Program.greedyWord B1 B2 r.1 r.2)
    (cache := fun r : Call × List Bool => mainFieldBits B1 B2 r.1)
    (budget := fun r : Call × List Bool => mainFieldCost B1 B2 r.1 r.2)
    (mainFieldWordFunction B1 B2)

end NearQuarticWires.StageMain
