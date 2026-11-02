import Proof.Quartic.StageCertNative.PriceFinite
import Proof.Quartic.StageCertNative.CountedSourceMachine
import Proof.Quartic.StageCert.MomentRuntimeScale

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells
open StageCert.Tokens

private theorem readFieldsCost_word (values : List ℕ) :
    StageGamma.readFieldsCost values≤
      40*(values.flatMap natWord).length+1 := by
  induction values with
  | nil => simp [StageGamma.readFieldsCost]
  | cons v values ih =>
    simp only [StageGamma.readFieldsCost,List.flatMap_cons,List.length_append,
      natWord_length]
    omega

theorem price_countedRead (B1 B2 : ℕ) :
    JobPrice (fun r : TermJob B1 B2=>countedReadSteps r.moment (termCount r.base)) 0 := by
  have hR:=price_runtimeScale B1 B2
  have hW:=price_wordLength B1 B2
  have hh:=(((JobPrice.constant 110000).mul (hR.pow 3)).add
    ((JobPrice.constant 80).mul hW)).add (JobPrice.constant 122)
  refine hh.mono ?_
  intro r
  have hprefix : (natWord r.index.val++natWord (termCount r.base)).length≤r.word.length := by
    unfold TermJob.word cachedSourceWord
    simp only [List.length_append]
    omega
  have hvalues : ((indexedMomentValues r.moment).flatMap natWord).length≤r.word.length := by
    rw [r.word_layout,List.length_append]
    unfold countedIndexedWord
    simp only [List.length_append]
    omega
  have hf:=readFieldsCost_word [r.index.val,termCount r.base]
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil] at hf
  have hg:=readFieldsCost_word (indexedMomentValues r.moment)
  have hi : StageMain.Compact.initializeCost r.moment.call r.moment.selected.1
      r.moment.retainedWitness (Program.prepWord B1 B2 r.moment.call r.moment.witness).length≤
      110000*r.moment.runtimeScale^3 := by
    rw [StageMain.Compact.prepWord_eq_compact r.moment.dispatched] 
    exact (show _≤r.moment.readSteps by
      unfold MomentRequest.readSteps
      rw [StageMain.Compact.prepWord_eq_compact r.moment.dispatched]
      omega).trans r.moment.readSteps_le
  unfold countedReadSteps
  change StageGamma.readFieldsCost [r.index.val,termCount r.base]+_+_+120≤_
  omega

theorem price_countedSourceSteps (B1 B2 : ℕ) :
    JobPrice (fun r : TermJob B1 B2=>countedSourceSteps r.moment (termCount r.base)) 0 := by
  have hp:=(price_wordLength B1 B2).mono (fun r=>
    r.moment.prep_length_le.trans (by
      have h:=r.word_layout
      have hh:=countedIndexedWord_length r.moment (termCount r.base)
      rw [h,List.length_append,hh]
      omega))
  exact (((price_countedRead B1 B2).add ((JobPrice.constant 9).mul hp)).add
    ((JobPrice.constant 6).mul (((JobPrice.constant 40).mul
      ((price_wordLength B1 B2).mono (fun r=>by
        rw [r.word_layout,List.length_append,countedIndexedWord_length]
        omega))).add (JobPrice.constant 43)))).add (JobPrice.constant 9)

theorem price_jobSource (B1 B2 : ℕ) :
    JobPrice (@jobSourceBudget B1 B2) 0 := by
  exact (price_wordLength B1 B2).finite
    (((JobPrice.constant 3).mul (price_countedSourceSteps B1 B2)).add (JobPrice.constant 8))
    StageRecovery.packetCallee VV MM

end NearQuarticWires.StageCertNative
