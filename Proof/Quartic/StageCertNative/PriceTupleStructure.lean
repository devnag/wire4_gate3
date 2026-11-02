import Proof.Quartic.StageCertNative.PriceCuts
import Proof.Quartic.StagePrintTuple.TermStageContract
import Proof.Quartic.Cells.AsymptoticsOccurrences

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces

private theorem entry_setup_bound {modular : Bool} (e : StagePrint.EntryFormat.Request modular) :
    e.termRequest.setupStructuralMagnitude≤e.header.call.n+e.termRequest.stackWidth+
      e.contextWord.length+(natWord e.walkCode.val).length+(natWord e.degree).length+10 := by
  have hctx : e.termRequest.contextWord.length=e.countsWord.length+(natWord e.walkCode.val).length := by
    simp only [StageTuple.TermCutRequest.contextWord,StagePrint.EntryFormat.Request.countsWord,
      List.flatMap_cons,List.flatMap_nil,List.append_nil,List.length_append,Nat.add_assoc]
    rfl
  have hf : (callWord e.header.call).length+
      ((StagePrint.Header.baseHeaderValues e.header).flatMap natWord).length+
      e.countsWord.length≤e.contextWord.length := by
    unfold StagePrint.EntryFormat.Request.contextWord
    simp only [NearCubicWires.WireExponent3_5.CompilerMachine.Top.loadRec,List.length_append,
      frame_length,List.length_nil]
    omega
  unfold StageTuple.TermCutRequest.setupStructuralMagnitude
  rw [hctx]
  change e.header.call.n+e.termRequest.stackWidth+(callWord e.header.call).length+
    ((StagePrint.Header.baseHeaderValues e.header).flatMap natWord).length+
    (e.countsWord.length+(natWord e.walkCode.val).length)+(natWord e.degree).length+10≤_
  omega

theorem price_walkWordLength (B1 B2 : ℕ) :
    JobPrice (fun r : TermJob B1 B2=>(natWord r.index.val).length) 0 := by
  have hh:=((JobPrice.constant 2).mul (price_prefixScalarBits B1 B2)).add (JobPrice.constant 1)
  refine hh.mono ?_
  intro r
  rw [natWord_length]
  unfold prefixScalarBits
  omega

theorem price_tupleSetupMagnitude (B1 B2 : ℕ) :
    JobPrice (fun r : TermJob B1 B2=>(termRequest r.base r.index).setupStructuralMagnitude) 0 := by
  have hc : JobPrice (fun r : TermJob B1 B2=>(exactEntry r.moment).contextWord.length) 0 := by
    refine (price_contextLength B1 B2).mono ?_
    intro r
    exact le_of_eq (congrArg List.length (actualEntry_context r.base r.index))
  have hh:=(((((price_arity B1 B2).add (price_stackWidth B1 B2)).add hc).add
    (price_walkWordLength B1 B2)).add (price_degree B1 B2).natWordLength).add (JobPrice.constant 10)
  exact hh.mono (fun r=>entry_setup_bound (exactEntry r.moment))

theorem price_childCap (B1 B2 : ℕ) :
    JobPrice (fun r : TermJob B1 B2=>r.moment.selected.1.childCap) 0 := by
  refine JobPrice.of_arity ⟨8,3,fun r=>?_⟩
  have hh:=r.moment.rules.childCap_le
  have hl : r.moment.selected.1.lambda≤r.moment.call.n := by
    rw [r.moment.rules.lambda_eq]
    exact NearCubicGates.Close.Counter.clog_le_self _
  have hb:=hh.trans (Nat.mul_le_mul_left _ hl)
  calc
    _≤8*r.moment.call.n^2*r.moment.call.n := hb
    _=8*r.moment.call.n^3 := by ring
    _≤_ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_succ _) _)

theorem price_tupleCensusMagnitude (B1 B2 : ℕ) :
    JobPrice (fun r : TermJob B1 B2=>(termRequest r.base r.index).censusMagnitude
      r.moment.selected.1.childCap) 0 := by
  have hrow:=(JobPrice.constant 2).mul (price_nativeWidth B1 B2)
  exact (((((price_tupleSetupMagnitude B1 B2).add hrow).add (price_degree B1 B2)).add
    (price_poolArity B1 B2)).add (price_childCap B1 B2)).add (JobPrice.constant 1)

end NearQuarticWires.StageCertNative
