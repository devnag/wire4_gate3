import Proof.Quartic.StageCompiledTerms.SmallCosts
import Proof.Quartic.Reconstruct.BatchLoopStages

set_option autoImplicit false

namespace NearQuarticWires.StageCompiledTerms

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces.Formats
open NearQuarticWires.Control NearQuarticWires.Reconstruct.Batch

/-- Step 3, `sec:algorithm`, paper/paper.tex: the proof
schedule is precisely the original finite walk census. -/
theorem walkRequests_length {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    (walkRequests r).length=r.child.cellCall.seed.N^8 := by simp only [walkRequests,List.length_ofFn]

/-- Step 3, `sec:algorithm`, paper/paper.tex: each actual
scheduled packet retains the same original request and preparation. -/
theorem walkRequests_parent {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2)
    (w : WalkRequest B1 B2) (hw : w∈walkRequests r) : w.1=r := by
  obtain ⟨index,rfl⟩:=List.mem_ofFn.mp hw
  rfl

/-- `prop:time`, paper/paper.tex: the
maximum actual compiler clock remains below the selected uniform bound. -/
theorem compilerMaximum_le_unit {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    compilerMaximum r≤unitBudget r := by
  have hall : ∀ value∈(walkRequests r).map packetCompilerBudget,value≤unitBudget r := by
    intro value hv
    obtain ⟨w,hw,rfl⟩:=List.mem_map.mp hv
    have h:=packetCompilerBudget_le_unit w
    rwa [walkRequests_parent r w hw] at h
  unfold compilerMaximum
  generalize (walkRequests r).map packetCompilerBudget=values at *
  induction values with
  | nil=>simp
  | cons value values ih=>
    exact max_le (hall value (by simp)) (ih (fun v hv=>hall v (by simp [hv])))

/-- `lem:print`, paper/paper.tex: a paid
entry tag uses only actual encoded source-header bytes. -/
theorem walkTag_length {B1 B2 : ℕ} (w : WalkRequest B1 B2) :
    (walkTag w).length≤(walkInput w).length := by
  simp only [walkTag,packetTag,walkInput,StageFormulaMetadata.RawWalkPacket.word,
    List.flatMap_cons,List.flatMap_nil,List.append_nil,List.length_append]
  omega

/-- `prop:time`, paper/paper.tex: every
source/input/tag byte and every actual compiler reply has its proved
selected bound; no output-length field is supplied to the machine. -/
theorem walk_request_bounds {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2)
    (w : WalkRequest B1 B2) (hw : w∈walkRequests r) :
    (walkInput w).length≤unitBudget r ∧ (walkTag w).length≤unitBudget r ∧
      (walkAnswer w).length≤unitBudget r+1 := by
  have hi' : (walkInput w).length≤unitBudget w.1 := by
    have h:=sourcePacketBound_spec w.1 w.2
    have h':=sourcePacketBound_le_unit w.1
    change (walkInput w).length + 1 ≤ sourcePacketBound w.1 at h
    omega
  have ho:=Control.output_length_le (packetCompilerWordFunction B1 B2) w
  change (walkAnswer w).length≤packetCompilerBudget w+1 at ho
  have hb:=packetCompilerBudget_le_unit w
  have he:=walkRequests_parent r w hw
  rw [he] at hi' hb
  exact ⟨hi',(walkTag_length w).trans hi',by omega⟩

/-- `prop:time`, paper/paper.tex: the full
actual ordinary batch clock is linear in walk census and the actual
per-packet source/compiler envelope, including all cleanup and copies. -/
theorem compiledBatchSteps_le {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    compiledBatchSteps r≤10^6*r.child.cellCall.seed.N^8*unitBudget r := by
  let U:=unitBudget r
  let N:=(walkRequests r).length
  have hU : 1≤U := by dsimp only [U,unitBudget];omega
  have hN : 1≤N := by simpa only [N,walkRequests_length] using StageLiftSourceCost.walkCount_pos r
  have hNU : 1≤N*U:=Nat.mul_pos hN hU
  have hNle : N≤N*U:=Nat.le_mul_of_pos_right _ hU
  have hUle : U≤N*U:=Nat.le_mul_of_pos_left _ hN
  have hsmall:=small_source_costs r
  have hpre : (batchContext r).length≤U:=hsmall.1
  have hcount : (natWord N).length≤U := by simpa only [N,walkRequests_length] using hsmall.2.1
  have hB : compilerMaximum r≤U:=compilerMaximum_le_unit r
  have hitems:=itemsCost_le walkTag walkInput (compilerMaximum r)
    (fun w=>answerCopyCost (termsWord (StagePrint.TermsCarrier.actualTerms w.1 w.2)))
    (walkRequests r) (100000*U) (by
      intro w hw
      obtain ⟨hi,ht,ho⟩:=walk_request_bounds r w hw
      change (walkInput w).length≤U at hi
      change (walkTag w).length≤U at ht
      change (walkAnswer w).length≤U+1 at ho
      have hcp : answerCopyCost (termsWord (StagePrint.TermsCarrier.actualTerms w.1 w.2))≤210*U := by
        change 100*(walkAnswer w).length+10≤210*U
        omega
      unfold itemCost callCost cleanCost
      change _≤100000*U
      omega)
  have hout:=batchOut_length (batchContext r) walkTag walkAnswer (walkRequests r) (2*U+1)
    (by intro w hw;have h:=walk_request_bounds r w hw;omega)
  change itemsCost _ _ _ _ _≤N*(100000*U)+1 at hitems
  change (batchOut _ _ _ _).length≤(batchContext r).length+(natWord N).length+N*(2*U+1) at hout
  have hout' : (batchOut (batchContext r) walkTag walkAnswer (walkRequests r)).length≤5*N*U := by
    nlinarith only [hout,hpre,hcount,hNle,hUle]
  change batchCost (batchContext r) walkTag walkInput walkAnswer (compilerMaximum r)
    (fun w=>answerCopyCost (termsWord (StagePrint.TermsCarrier.actualTerms w.1 w.2)))
    (walkRequests r)≤10^6*r.child.cellCall.seed.N^8*U
  rw [←walkRequests_length]
  change _≤10^6*N*U
  unfold batchCost
  nlinarith only [hitems,hpre,hcount,hout',hNU,hUle]

end NearQuarticWires.StageCompiledTerms
