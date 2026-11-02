import Proof.Quartic.StageLift.AllWalks

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells

/-- Step 3 and `lem:print`, paper/paper.tex: one actual cold source reads the original print input,
retains its finite preparation once and synthesizes every original
walk's complete indexed integer Formula packet. -/
def printFormulaSourceProgram : St VV MM := .seq coldCarrierInitialize emitAllWalkPackets

/-- Step 3, `lem:print` and `prop:time`, paper/paper.tex: the complete source program
starts from the blank state and emits the exact frozen one-copy carrier
and all original packets. No decoded source, Formula, coefficient table,
flag stream, count, hint or assumed body is an extra runtime input. -/
theorem printFormulaSourceProgram_spec {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    let C := printSourceContext B1 B2 (Greedy.printInput r)
    Hs C printFormulaSourceProgram (a0 : DS VV MM) (sourceProgramSteps r)
      (fun z => z.out = sourceCarrierWord r) := by
  dsimp only
  let C := printSourceContext B1 B2 (Greedy.printInput r)
  unfold printFormulaSourceProgram
  refine (Hs.seq (t1 := carrierStartupCost r + 6)
    (t2 := allWalkSourceCost r C.Lk C.Bk) (coldCarrierInitialize_spec r)
    fun a ⟨hao,hasource,_haend,hakin,hac,hav⟩ => ?_).mono ?_ (fun _ h => h)
  · refine (emitAllWalkPackets_spec r a hasource hac hav hakin).mono le_rfl ?_
    rintro z ⟨hzo,_hzstate,_hzI,_hzN,_hzip⟩
    rw [hzo,hao]
    simp only [sourceCarrierWord,List.append_assoc]
  · change (carrierStartupCost r + 6) + allWalkSourceCost r C.Lk C.Bk + 1 ≤
      carrierStartupCost r + 6 + allWalkSourceCost r C.Lk C.Bk + 1
    exact le_rfl

/-- `lem:print` and `prop:time`, paper/paper.tex: an actual fixed ordinary multitape machine synthesizes
the entire original source carrier from literal Greedy.printInput. Its
budget includes real header allocation, compilation, structural callees
and head restoration; there is no additional algorithm premise. -/
noncomputable def printFormulaSourceWordFunction (B1 B2 : ℕ) :
    WordFunction (Greedy.PrintRequest B1 B2) Greedy.printInput sourceCarrierWord sourceMachineBudget :=
  wordFunction_of_lang Greedy.printInput sourceCarrierWord
    (StageCert.Tokens.structuralSourceCallee B1 B2) (printSourceSizes B1 B2)
    printFormulaSourceProgram sourceProgramSteps (by
      intro r
      obtain ⟨z,n,he,hn,hout⟩ := printFormulaSourceProgram_spec r
      exact ⟨z,n,he,hout,hn⟩) (by
      intro r
      have h := printSourceSizes_width r []
      have hp : 1 ≤ (sourceEnvelope r + 1) ^ 2 := Nat.pow_pos (by omega)
      simpa only [List.append_nil] using (show 1 ≤
        (printSourceSizes B1 B2).W (leadOnes (Greedy.printInput r ++ [])) by omega))

end NearQuarticWires.StageLift
