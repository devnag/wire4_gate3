import Proof.Quartic.StageCertNative.PriceCuts
import Proof.Quartic.StageCertNative.PriceLanguage
import Proof.Quartic.StageCertNative.TupleJoin

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells

theorem price_equalityEntryLength (B1 B2 : ℕ) :
    JobPrice (fun r : TermJob B1 B2=>(equalityEntryWord r).length) 1 := by
  have hh:=(price_exactEntryLength B1 B2).add
    (((JobPrice.constant 2).mul (price_tupleOutput B1 B2)).add
      ((JobPrice.constant 1).raise (by decide : 0≤1)))
  simpa only [equalityEntryWord,List.length_append,frame_length] using hh

theorem price_entryReaderSteps (B1 B2 : ℕ) :
    JobPrice (fun r : TermJob B1 B2=>StagePrint.EntryFormat.readerSteps (exactEntry r.moment)) 1 := by
  have hh:=(JobPrice.constant 10000).mul
    (((price_exactEntryLength B1 B2).add ((price_sizingMagnitude B1 B2).raise
      (by decide : 0≤1))).add ((JobPrice.constant 1).raise (by decide : 0≤1)))
  refine hh.mono ?_
  intro r
  have hr : StagePrint.EntryFormat.readerSteps (exactEntry r.moment)≤
      StagePrint.EntryFormat.coldSteps (exactEntry r.moment) := by
    unfold StagePrint.EntryFormat.coldSteps
    omega
  exact hr.trans (StagePrint.EntryFormat.coldSteps_linear (exactEntry r.moment))

theorem price_equalityProgramSteps (B1 B2 : ℕ) :
    JobPrice (@equalityProgramSteps B1 B2) 1 := by
  have hn:=(price_arity B1 B2).add (JobPrice.constant 1)
  have hn':=hn.mono (fun r=>Nat.div_le_self (r.moment.call.n+1) 2)
  exact ((JobPrice.constant 3).mul
    (((((price_entryReaderSteps B1 B2).add ((JobPrice.constant 11).mul
      (price_tupleOutput B1 B2))).add (((JobPrice.constant 9).mul hn').raise
      (by decide : 0≤1))).add (((JobPrice.constant 9).mul (price_stackWidth B1 B2)).raise
      (by decide : 0≤1))).add ((JobPrice.constant 60).raise (by decide : 0≤1)))).add
    ((JobPrice.constant 8).raise (by decide : 0≤1))

private theorem equality_header {B1 B2 : ℕ} (r : TermJob B1 B2) :
    leadOnes (equalityEntryWord r)=natBitLength r.moment.call.n := by
  unfold equalityEntryWord StagePrint.EntryFormat.Request.word
  simp only [List.append_assoc]
  exact NearCubicGates.Close.CounterMachine.PrefixProg.leadOnes_natWord _ _

theorem price_equalityFormat (B1 B2 : ℕ) :
    JobPrice (@equalityFormatBudget B1 B2) 1 := by
  have hh : JobPrice (fun r : TermJob B1 B2=>leadOnes (equalityEntryWord r)) 0 := by
    simpa only [equality_header] using (price_arity B1 B2).natBits
  have hw : JobPrice (fun r : TermJob B1 B2=>
      (equalitySizes B1 B2).W (leadOnes (equalityEntryWord r))) 0 := by
    refine JobPrice.of_arity ⟨10*(entrySizingCoefficient B1 B2+1)*
      2^(entrySizingExponent B1 B2+2),entrySizingExponent B1 B2+2,fun r=>?_⟩
    rw [equality_header]
    exact StageEntryAllocation.width_polynomial _ _ _
  have hl : JobPrice (fun r : TermJob B1 B2=>
      (equalitySizes B1 B2).Lk (leadOnes (equalityEntryWord r))) 0 := by
    simpa only [equalitySizes,StageEntryAllocation.sizes,Sz.Lk,Nat.mul_zero] using
      (JobPrice.constant (B1:=B1) (B2:=B2) 0)
  have hb : JobPrice (fun r : TermJob B1 B2=>
      (equalitySizes B1 B2).Bk (leadOnes (equalityEntryWord r))) 0 := by
    simpa only [equalitySizes,StageEntryAllocation.sizes,Sz.Bk,Nat.mul_zero] using
      (JobPrice.constant (B1:=B1) (B2:=B2) 0)
  exact (price_equalityEntryLength B1 B2).language (price_equalityProgramSteps B1 B2)
    StageRecovery.packetCallee (equalitySizes B1 B2) VV MM hh hw hl hb

section
variable {B1 B2 : ℕ} {tupleBudget : StageTuple.TermCutRequest→ℕ}
variable (htuple : JobPrice (fun r : TermJob B1 B2=>tupleBudget (termRequest r.base r.index)) 2)
include htuple

theorem price_tupleSource : JobPrice (@tupleSourceBudget tupleBudget B1 B2) 4 :=
  (((JobPrice.constant 4).mul (price_termRequestSource B1 B2)).add
    (((JobPrice.constant 4).mul htuple).raise (by decide : 2≤4))).add
    ((JobPrice.constant 12).raise (by decide : 0≤4))

theorem price_nestedTuple : JobPrice (@nestedTupleBudget tupleBudget B1 B2) 4 :=
  (((JobPrice.constant 4).mul (price_tupleSource htuple)).add
    (((JobPrice.constant 4).mul (((JobPrice.constant 2000).mul
      ((price_tupleOutput B1 B2).add ((JobPrice.constant 1).raise (by decide : 0≤1)))).add
      ((JobPrice.constant 2).raise (by decide : 0≤1)))).raise (by decide : 1≤4))).add
    ((JobPrice.constant 12).raise (by decide : 0≤4))

theorem price_equalitySource : JobPrice (@equalitySourceBudget tupleBudget B1 B2) 4 := by
  have hr : JobPrice (fun r : TermJob B1 B2=>(frame (termRequest r.base r.index).output).length) 4 := by
    have hh:=(((JobPrice.constant 2).mul (price_tupleOutput B1 B2)).add
      ((JobPrice.constant 1).raise (by decide : 0≤1))).raise (by decide : 1≤4)
    simpa only [frame_length] using hh
  exact ((price_wordLength B1 B2).raise (by decide : 0≤4)).framedPair
    ((price_exactEntryLength B1 B2).raise (by decide : 1≤4)) hr
    (price_entrySource B1 B2) (price_nestedTuple htuple)

theorem price_equalityJob : JobPrice (@equalityJobBudget tupleBudget B1 B2) 4 :=
  (((JobPrice.constant 4).mul (price_equalitySource htuple)).add
    (((JobPrice.constant 4).mul (price_equalityFormat B1 B2)).raise (by decide : 1≤4))).add
    ((JobPrice.constant 12).raise (by decide : 0≤4))

theorem price_weakTerm : JobPrice (@weakTermBudget tupleBudget B1 B2) 4 := by
  have hdim:=((price_nativeWidth B1 B2).add (price_stackWidth B1 B2)).add
    (JobPrice.constant 2)
  have hrow:=(JobPrice.constant (10^30)).mul (hdim.pow 20)
  have hinput:=((price_tupleOutput B1 B2).add ((JobPrice.constant 1).raise
    (by decide : 0≤1))).pow 2
  have he:=hrow.mul hinput
  have he' : JobPrice (fun r : TermJob B1 B2=>10^30*
      (NearCubicWires.WireExponent3_5.PrimT.C4Geo.width
        (termNativeRequest r).parameters+(termNativeRequest r).fieldWidth+2)^20*
        (((termNativeRequest r).cuts.flatMap
          (MatrixScoreBatch.cutWord (termNativeRequest r).fieldWidth)).length+1)^2) 2 := by
    refine he.mono ?_
    intro r
    have hw : ((termNativeRequest r).cuts.flatMap
        (MatrixScoreBatch.cutWord (termNativeRequest r).fieldWidth)).length=
        (termRequest r.base r.index).output.length :=
      congrArg List.length (StagePrint.nativeEqualityCuts_word (termRequest r.base r.index))
    rw [hw]
    exact le_rfl
  exact (((JobPrice.constant 4).mul (price_equalityJob htuple)).add
    (((JobPrice.constant 4).mul he').raise (by decide : 2≤4))).add
    ((JobPrice.constant 12).raise (by decide : 0≤4))

end
end NearQuarticWires.StageCertNative
