import Proof.Quartic.StagePrintTuple.MonomialReadyExact

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close.WordPrograms
open NearQuarticWires.Control

/-- `lem:print` and `prop:time`, paper/paper.tex: actual monomial acquisition supplies every literal
cache and blank-bank precondition of physical preparation, giving the
canonical original-term reverse-loop start without added source data. -/
theorem kernelMonomialPrepare_run (r : TermCutRequest) (span k cap : ℕ) (hk : k<r.terms.length)
    (hp : coefficientWordFunction.program.tapeCount ≤ span)
    (hcap : monomialPrepareCapacity (r.stackWidth+1)
      (((r.terms[k]'hk).1.sort (·≤·)).map Fin.val) (r.terms[k]'hk).2 ≤ cap) :
    let support : List ℕ := ((r.terms[k]'hk).1.sort (·≤·)).map Fin.val
    let coefficient : ℤ := (r.terms[k]'hk).2
    let σ0 : WState (span+29) 32 := ((r.progressData k).state span r).setv 17 (r.terms.length-(k+1))
    let P : Fin 3↪Fin (span+30) := kernelExternalMap span kernelMonomialSources
    let σ : WState (span+29) 32 := monomialAcquireState P (r.stackWidth+1) support coefficient (r.termsPrefix k) σ0
    ∃τ,WXExec cap (monomialPrepareProgram span hp) σ τ
      (monomialPrepareCost (r.stackWidth+1) support coefficient) ∧
      SimW ((r.progressMonomial k hk).reverseState r span 0) τ := by
  let support : List ℕ := ((r.terms[k]'hk).1.sort (·≤·)).map Fin.val
  let coefficient : ℤ := (r.terms[k]'hk).2
  let σ0 : WState (span+29) 32 := ((r.progressData k).state span r).setv 17 (r.terms.length-(k+1))
  let P : Fin 3↪Fin (span+30) := kernelExternalMap span kernelMonomialSources
  let σ : WState (span+29) 32 := monomialAcquireState P (r.stackWidth+1) support coefficient (r.termsPrefix k) σ0
  let s := kernelSite span coefficientWordFunction.program hp
  have b0 : CallBlank coefficientWordFunction.program s σ0 :=
    ((r.progressData k).state_blank span r _ hp).setv 17 _ (by
      intro i;fin_cases i <;> simp [kernelSite,kernelCallRegisters])
  have blank : CallBlank coefficientWordFunction.program s σ :=
    (((b0.sets (kernelLocal span 14) _ (kernelSite_out span _ hp 14 (by decide) (by decide))
      (kernelSite_ruler_ne span _ hp 14 (by decide))).sets (kernelLocal span 15) _
      (kernelSite_out span _ hp 15 (by decide) (by decide))
      (kernelSite_ruler_ne span _ hp 15 (by decide))).seth (kernelLocal span 5) _
      (kernelSite_out span _ hp 5 (by decide) (by decide))
      (kernelSite_ruler_ne span _ hp 5 (by decide)))
  obtain ⟨τ,et,ht⟩ := monomialPrepareProgram_spec span cap (r.stackWidth+1) hp support coefficient σ blank
    (by simp [σ,monomialAcquireState,P,kernelExternalMap,kernelMonomialSources,kernelLocal])
    (by simp [σ,σ0,monomialAcquireState,P,kernelExternalMap,kernelMonomialSources,kernelLocal,
      KernelData.state,TermCutRequest.progressData])
    (by simp [σ,monomialAcquireState,P,kernelExternalMap,kernelMonomialSources,kernelLocal])
    (by simp [σ,σ0,monomialAcquireState,P,kernelExternalMap,kernelMonomialSources,kernelLocal,
      KernelData.state,TermCutRequest.progressData])
    (by simp [σ,σ0,monomialAcquireState,P,kernelExternalMap,kernelMonomialSources,kernelLocal,
      KernelData.state,TermCutRequest.progressData])
    (by simp [σ,σ0,monomialAcquireState,P,kernelExternalMap,kernelMonomialSources,kernelLocal,
      KernelData.state,TermCutRequest.progressData])
    (by intro i;fin_cases i <;> simp [σ,σ0,monomialAcquireState,KernelData.state,TermCutRequest.progressData])
    (by simp [σ,σ0,monomialAcquireState,KernelData.state,TermCutRequest.progressData])
    (by simp [σ,σ0,monomialAcquireState,KernelData.state,TermCutRequest.progressData])
    (by simp [σ,σ0,monomialAcquireState,KernelData.state,TermCutRequest.progressData])
    (by simp [σ,σ0,monomialAcquireState,KernelData.state,TermCutRequest.progressData]) hcap
  have he : monomialPrepareState span (r.stackWidth+1) support coefficient σ=
      (r.progressMonomial k hk).reverseState r span 0 := monomialReadyExact r span k hk
  rw [he] at ht
  exact ⟨τ,et,ht⟩

end NearQuarticWires.StageTuple
