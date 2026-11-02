import Proof.Quartic.StagePrintTuple.KernelMonomialSource
import Proof.Quartic.StagePrintTuple.MonomialPrepare

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.WordPrograms

/-- `lem:print`, paper/paper.tex: one actual
monomial byte count advances the genuine Terms prefix by precisely
its support codec and original signed coefficient codec. -/
theorem TermCutRequest.termsPrefix_succ (r : TermCutRequest) (k : ℕ) (hk : k<r.terms.length) :
    r.termsPrefix (k+1)=r.termsPrefix k++monoWord r.terms[k] := by
  unfold TermCutRequest.termsPrefix
  rw [List.take_succ_eq_append_getElem hk,List.flatMap_append,List.flatMap_singleton,List.append_assoc]

/-- `lem:print`, paper/paper.tex: actual source
acquisition and physical monomial preparation establish exactly the
complete initial reverse-loop state for the original current term. -/
theorem monomialReadyExact (r : TermCutRequest) (span k : ℕ) (hk : k<r.terms.length) :
    let support := (r.terms[k].1.sort (·≤·)).map Fin.val
    let coefficient := r.terms[k].2
    let σ := ((r.progressData k).state span r).setv 17 (r.terms.length-(k+1))
    let P := kernelExternalMap span kernelMonomialSources
    monomialPrepareState span (r.stackWidth+1) support coefficient
      (monomialAcquireState P (r.stackWidth+1) support coefficient (r.termsPrefix k) σ)=
      (r.progressMonomial k hk).reverseState r span 0 := by
  dsimp only
  have hcursor := congrArg List.length (r.termsPrefix_succ k hk)
  simp only [List.length_append,monoWord] at hcursor
  have hlen : ((r.terms[k].1.sort (·≤·)).map Fin.val).length=r.terms[k].1.card := by
    simp
  have hpref : ((r.terms[k].1.sort (·≤·)).map Fin.val).length=
      (r.terms[k].1.sort (·≤·)).length := by simp only [List.length_map]
  have hsort : (r.terms[k].1.sort (·≤·)).length=r.terms[k].1.card := by simp
  have hdrop : (r.terms[k].1.sort (·≤·)).drop r.terms[k].1.card=[] := by
    rw [←hsort]
    exact List.drop_length
  apply WState.eq
  · funext i
    by_cases hi5:i.val=5
    · have he:i=kernelLocal span 5 := Fin.ext hi5
      subst i
      simp [monomialPrepareState,monomialAcquireState,kernelExternalMap,kernelMonomialSources,
        kernelLocal,MonomialData.reverseState,MonomialData.reverseData,KernelData.state,
        TermCutRequest.progressMonomial,TermCutRequest.progressData,hcursor]
    · by_cases hi14:i.val=14
      · have he:i=kernelLocal span 14 := Fin.ext hi14
        subst i
        simp [monomialPrepareState,monomialAcquireState,kernelExternalMap,kernelMonomialSources,
          kernelLocal,MonomialData.reverseState,MonomialData.reverseData,KernelData.state,
          TermCutRequest.progressMonomial,TermCutRequest.progressData,hpref]
      · by_cases hrange : 14 ≤ i.val ∧ i.val < 20
        · have hlo : 15 ≤ i.val := by omega
          have hup : i.val ≤ 19 := by omega
          generalize hvalue : i.val=z at *
          interval_cases z <;>
            simp [monomialPrepareState,monomialAcquireState,kernelExternalMap,kernelMonomialSources,
              kernelLocal,MonomialData.reverseState,MonomialData.reverseData,KernelData.state,
              TermCutRequest.progressMonomial,TermCutRequest.progressData,Fin.ext_iff,
              tupleHistoryPrefix,tupleHistory,tupleSegment,processedSupport,tupleFields_nil,hdrop,
              NearCubicGates.Close.TabMachine.fieldsRecs,Function.update_apply,hvalue]
        · simp [monomialPrepareState,monomialAcquireState,kernelExternalMap,kernelMonomialSources,
            kernelLocal,MonomialData.reverseState,MonomialData.reverseData,KernelData.state,
            TermCutRequest.progressMonomial,TermCutRequest.progressData,Fin.ext_iff,hi5,hi14,hrange,
            tupleHistoryPrefix,tupleHistory,tupleSegment,processedSupport,tupleFields_nil,hdrop,NearCubicGates.Close.TabMachine.fieldsRecs]
  · funext i
    by_cases hi14:i.val=14
    · have he:i=kernelLocal span 14 := Fin.ext hi14
      subst i
      simp [monomialPrepareState,monomialAcquireState,kernelExternalMap,kernelMonomialSources,
        kernelLocal,MonomialData.reverseState,MonomialData.reverseData,KernelData.state,
        TermCutRequest.progressMonomial,TermCutRequest.progressData]
    · by_cases hi15:i.val=15
      · have he:i=kernelLocal span 15 := Fin.ext hi15
        subst i
        simp [monomialPrepareState,monomialAcquireState,kernelExternalMap,kernelMonomialSources,
          kernelLocal,MonomialData.reverseState,MonomialData.reverseData,KernelData.state,
          TermCutRequest.progressMonomial,TermCutRequest.progressData,CoefficientRequest.word]
      · by_cases hi16:i.val=16
        · have he:i=kernelLocal span 16 := Fin.ext hi16
          subst i
          simp [monomialPrepareState,monomialAcquireState,kernelExternalMap,kernelMonomialSources,
            kernelLocal,MonomialData.reverseState,MonomialData.reverseData,KernelData.state,
            TermCutRequest.progressMonomial,TermCutRequest.progressData]
        · by_cases hrange : 14 ≤ i.val ∧ i.val < 20
          · have hlo : 17 ≤ i.val := by omega
            have hup : i.val ≤ 19 := by omega
            generalize hvalue : i.val=z at *
            interval_cases z <;>
              simp [monomialPrepareState,monomialAcquireState,kernelExternalMap,kernelMonomialSources,
                kernelLocal,MonomialData.reverseState,MonomialData.reverseData,KernelData.state,
                TermCutRequest.progressMonomial,TermCutRequest.progressData,Fin.ext_iff,
                tupleHistoryPrefix,tupleHistory,tupleSegment,processedSupport,tupleFields_nil,hdrop,
                  NearCubicGates.Close.TabMachine.fieldsRecs,Function.update_apply,hvalue]
          · simp [monomialPrepareState,monomialAcquireState,kernelExternalMap,kernelMonomialSources,
              kernelLocal,MonomialData.reverseState,MonomialData.reverseData,KernelData.state,
              TermCutRequest.progressMonomial,TermCutRequest.progressData,Fin.ext_iff,hi14,hi15,hi16,hrange,
              tupleHistoryPrefix,tupleHistory,tupleSegment,processedSupport,tupleFields_nil,hdrop,NearCubicGates.Close.TabMachine.fieldsRecs]
  · funext i
    fin_cases i <;> simp [monomialPrepareState,monomialAcquireState,MonomialData.reverseState,
      MonomialData.reverseData,KernelData.state,TermCutRequest.progressMonomial,
      TermCutRequest.progressData,hlen,processedSupport,tupleFields_nil,hdrop,NearCubicGates.Close.TabMachine.fieldsRecs]
  · rfl

end NearQuarticWires.StageTuple
