import Proof.Quartic.StageTupleMonomialFinish.KernelReset

set_option autoImplicit false

namespace NearQuarticWires.StageTupleMonomialFinish

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open StageTuple

/-- `lem:print`, paper/paper.tex: the literal
Stack, finite-cache and history updates are exactly the next monomial
boundary, with all six caches blank and all local counts zero. -/
theorem finishState_eq (span : ℕ) (r : TermCutRequest)
    (data : MonomialData (17*(Builder.allGates r.header.call).length))
    (t : Finset (Fin (17*(Builder.allGates r.header.call).length))×ℤ) (ht : t∈r.terms) :
    resetState span (cachesState span (stackState r data t ht span))=
      (data.finishedData r t ht).state span r := by
  apply WState.eq
  · funext i
    by_cases hi:i.val<30
    · let j : Fin 30 := ⟨i.val,hi⟩
      have hij:i=kernelLocal span j := rfl
      rw [hij]
      clear hij
      clear_value j
      fin_cases j <;> simp [resetState,nextHistoryState,cachesState,stackState,appendO,MonomialData.reverseState,MonomialData.reverseData,MonomialData.finishedData,KernelData.state,kernelLocal]
    · have h13 : ¬i.val<13 := by omega
      have h20 : ¬i.val<20 := by omega
      have he20 : i.val≠20 := by omega
      have he21 : i.val≠21 := by omega
      have he5 : i.val≠5 := by omega
      have he6 : i.val≠6 := by omega
      have he9 : i.val≠9 := by omega
      simp [resetState,nextHistoryState,cachesState,stackState,appendO,MonomialData.reverseState,MonomialData.reverseData,MonomialData.finishedData,KernelData.state,kernelLocal,Function.update_apply,Fin.ext_iff,h20,he20,he21,he5,he6,he9]
  · funext i
    by_cases hi:i.val<30
    · let j : Fin 30 := ⟨i.val,hi⟩
      have hij:i=kernelLocal span j := rfl
      rw [hij]
      clear hij
      clear_value j
      fin_cases j <;> simp [resetState,nextHistoryState,cachesState,stackState,appendO,MonomialData.reverseState,MonomialData.reverseData,MonomialData.finishedData,KernelData.state,kernelLocal]
    · have h13 : ¬i.val<13 := by omega
      have h20 : ¬i.val<20 := by omega
      have he20 : i.val≠20 := by omega
      have he21 : i.val≠21 := by omega
      have he5 : i.val≠5 := by omega
      have he6 : i.val≠6 := by omega
      have he9 : i.val≠9 := by omega
      simp [resetState,nextHistoryState,cachesState,stackState,appendO,MonomialData.reverseState,MonomialData.reverseData,MonomialData.finishedData,KernelData.state,kernelLocal,Function.update_apply,Fin.ext_iff,h13,h20,he20,he21]
  · funext i
    fin_cases i <;> simp [resetState,nextHistoryState,cachesState,stackState,appendO,MonomialData.reverseState,MonomialData.reverseData,MonomialData.finishedData,KernelData.state,kernelLocal]
  · rfl

end NearQuarticWires.StageTupleMonomialFinish
