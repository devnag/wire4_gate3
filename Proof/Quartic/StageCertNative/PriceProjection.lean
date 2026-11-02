import Proof.Quartic.StageCertNative.PriceEquality
import Proof.Quartic.StageCertNative.HeaderProjection

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells

private theorem tupleWord_length_le_cold {modular : Bool}
    (r : StagePrint.EntryFormat.Request modular) :
    r.termRequest.word.length≤StagePrint.EntryFormat.coldSteps r := by
  let C : Ctx:=⟨r.sizingMagnitude+10,r.word,StageRecovery.packetCallee,0,0⟩
  obtain ⟨b,n,he,hn,ho⟩:=StagePrint.EntryFormat.coldProgram_run C r rfl
    (by change r.sizingMagnitude+10≤r.sizingMagnitude+10;omega)
  have hh:=he.out_len
  simp only [a0,List.length_nil,zero_add] at hh
  rw [ho,frame_length] at hh
  omega

theorem price_tupleWord (B1 B2 : ℕ) :
    JobPrice (fun r : TermJob B1 B2=>(termRequest r.base r.index).word.length) 1 := by
  have hh:=(JobPrice.constant 10000).mul
    (((price_exactEntryLength B1 B2).add ((price_sizingMagnitude B1 B2).raise
      (by decide : 0≤1))).add ((JobPrice.constant 1).raise (by decide : 0≤1)))
  refine hh.mono ?_
  intro r
  exact (tupleWord_length_le_cold (exactEntry r.moment)).trans
    (StagePrint.EntryFormat.coldSteps_linear (exactEntry r.moment))

theorem price_stackProjection (B1 B2 : ℕ) :
    JobPrice (fun r : TermJob B1 B2=>stackProjectionBudget (termRequest r.base r.index)) 3 := by
  have hi : JobPrice (fun r : TermJob B1 B2=>
      (stackProjection (termRequest r.base r.index)).word.length) 1 := by
    simpa only [stackProjection_word] using price_tupleWord B1 B2
  exact hi.finite (((JobPrice.constant 300).mul (hi.add
      ((JobPrice.constant 1).raise (by decide : 0≤1)))).add
      ((JobPrice.constant 8).raise (by decide : 0≤1))) StageRecovery.packetCallee VV MM

theorem price_jobStack (B1 B2 : ℕ) : JobPrice (@jobStackBudget B1 B2) 4 :=
  (((JobPrice.constant 4).mul (price_termRequestSource B1 B2)).add
    (((JobPrice.constant 4).mul (price_stackProjection B1 B2)).raise (by decide : 3≤4))).add
    ((JobPrice.constant 12).raise (by decide : 0≤4))

theorem price_geometryProjection (B1 B2 : ℕ) :
    JobPrice (fun r : TermJob B1 B2=>geometryProjectionBudget r.base.prepared) 0 := by
  have hi : JobPrice (fun r : TermJob B1 B2=>
      (geometryProjection r.base.prepared).word.length) 0 := by
    simpa only [geometryProjection_word] using price_contextLength B1 B2
  exact hi.finite (((JobPrice.constant 300).mul (hi.add (JobPrice.constant 1))).add
    (JobPrice.constant 8)) StageRecovery.packetCallee VV MM

end NearQuarticWires.StageCertNative
