import Proof.Quartic.StageMain.FieldExtractProgram
import Proof.Quartic.StageGamma.FieldProducer

/-!
# Cold extraction of the unary field request

`imp:seed`, paper/paper.tex, and `prop:time`: one fixed ordinary machine reads the actual main source,
initializes arithmetic tapes from its arity header and prints the unary
degree used by the single primitive-field construction.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces

noncomputable def fieldExtractCost (B1 B2 : ℕ) (c : Call) (w : List Bool) : ℕ :=
  langBudget StageGamma.fieldProducerCallee (fieldExtractSizes B1 B2) VV MM
    (Program.greedyWord B1 B2 c w) (extractFieldSteps B1 B2 c w)

noncomputable def fieldExtractWordFunction (B1 B2 : ℕ) :
    WordFunction (Call × List Bool) (fun r => Program.greedyWord B1 B2 r.1 r.2)
      (fun r => frame (List.replicate (mainFieldDegree B1 B2 r.1) true))
      (fun r => fieldExtractCost B1 B2 r.1 r.2) := by
  unfold fieldExtractCost
  exact wordFunction_of_lang
    (fun r : Call × List Bool => Program.greedyWord B1 B2 r.1 r.2)
    (fun r : Call × List Bool => frame (List.replicate (mainFieldDegree B1 B2 r.1) true))
    StageGamma.fieldProducerCallee (fieldExtractSizes B1 B2)
    extractFieldProgram (fun r => extractFieldSteps B1 B2 r.1 r.2) (by
      intro r
      obtain ⟨b, n, he, hn, ho⟩ := extractFieldProgram_run B1 B2 r.1 r.2
        (ctxOf StageGamma.fieldProducerCallee (fieldExtractSizes B1 B2)
          (Program.greedyWord B1 B2 r.1 r.2)) rfl rfl
      exact ⟨b, n, he, ho, hn⟩) (by
      intro r
      have h := fieldExtractSizes_min B1 B2 (leadOnes (Program.greedyWord B1 B2 r.1 r.2))
      omega)

end NearQuarticWires.StageMain
