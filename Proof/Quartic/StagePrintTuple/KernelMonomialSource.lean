import Proof.Quartic.StagePrintTuple.TermsState
import Proof.Quartic.StagePrintTuple.MonomialAcquire
import Proof.Quartic.StagePrintTuple.KernelMaps

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.WordPrograms

/-- `lem:print`, paper/paper.tex: one actual
monomial is read directly from the retained Terms cursor into its two
finite support/coefficient cache tapes. -/
def kernelMonomialSources : Fin 3↪Fin 30 := ⟨![5,14,15],by decide⟩

/-- `prop:time`, paper/paper.tex: the local
monomial capacity depends only on its actual width, support codec and
signed coefficient codec, not the complete Terms bytes or count. -/
def monomialLocalCapacity (L : ℕ) (support : List ℕ) (coefficient : ℤ) : ℕ :=
  ([L+6*natBitLength L+6,2^(natBitLength support.length+1),support.length,
    support.length+6*natBitLength support.length+6,
    2*(listWord natWord support).length+3,
    2*(natWord L).length+2*(intWord coefficient).length+4] : List ℕ).sum

/-- `lem:print`, paper/paper.tex: the genuine
source at the current Terms prefix is exactly the next original
monomial followed by the literal remaining source bytes. -/
theorem TermCutRequest.terms_source_next (r : TermCutRequest) (k : ℕ) (hk : k<r.terms.length) :
    termsWord r.terms=r.termsPrefix k++monoWord r.terms[k]++
      (r.terms.drop (k+1)).flatMap monoWord := by
  have hflat : r.terms.flatMap monoWord=(r.terms.take k).flatMap monoWord++monoWord r.terms[k]++
      (r.terms.drop (k+1)).flatMap monoWord := by
    calc
      r.terms.flatMap monoWord=(r.terms.take k++r.terms.drop k).flatMap monoWord :=
        congrArg (List.flatMap monoWord) (List.take_append_drop k r.terms).symm
      _=_ := by rw [List.drop_eq_getElem_cons hk];simp only [List.flatMap_append,List.flatMap_cons,List.append_assoc]
  simp only [termsWord,listWord,hflat,TermCutRequest.termsPrefix,List.append_assoc]

/-- `lem:print` and `prop:time`, paper/paper.tex: the complete actual Terms boundary supplies the
monomial reader's literal input and local capacity, yielding both ready
caches at the next genuine source cursor with exact exterior state. -/
theorem kernelMonomialSource_run (r : TermCutRequest) (span k cap : ℕ) (hk : k<r.terms.length)
    (hcap : monomialLocalCapacity (r.stackWidth+1)
      ((r.terms[k].1.sort (·≤·)).map Fin.val) r.terms[k].2 ≤ cap) :
    let support := (r.terms[k].1.sort (·≤·)).map Fin.val
    let coefficient := r.terms[k].2
    let σ := ((r.progressData k).state span r).setv 17 (r.terms.length-(k+1))
    let P := kernelExternalMap span kernelMonomialSources
    WXExec cap (monomialAcquireProgram P kernelMonomialRegisters) σ
      (monomialAcquireState P (r.stackWidth+1) support coefficient (r.termsPrefix k) σ)
      (monomialAcquireCost (monomialLocalCapacity (r.stackWidth+1) support coefficient)
        (r.stackWidth+1) support coefficient) := by
  let support := (r.terms[k].1.sort (·≤·)).map Fin.val
  let coefficient := r.terms[k].2
  let small := monomialLocalCapacity (r.stackWidth+1) support coefficient
  let σ := ((r.progressData k).state span r).setv 17 (r.terms.length-(k+1))
  let P := kernelExternalMap span kernelMonomialSources
  apply monomialAcquireProgram_spec P kernelMonomialRegisters small cap (r.stackWidth+1) hcap
    support coefficient (r.termsPrefix k) ((r.terms.drop (k+1)).flatMap monoWord) σ
  · change σ.st (kernelLocal span 5)=_
    change termsWord r.terms=_
    simpa only [monoWord,support,coefficient,List.append_assoc] using r.terms_source_next k hk
  · change σ.sh (kernelLocal span 5)=_
    simp [σ,KernelData.state,TermCutRequest.progressData,kernelLocal]
  · change σ.st (kernelLocal span 14)=_
    simp [σ,KernelData.state,TermCutRequest.progressData,kernelLocal]
  · change σ.sh (kernelLocal span 14)=_
    simp [σ,KernelData.state,TermCutRequest.progressData,kernelLocal]
  · change σ.st (kernelLocal span 15)=_
    simp [σ,KernelData.state,TermCutRequest.progressData,kernelLocal]
  · change σ.sh (kernelLocal span 15)=_
    simp [σ,KernelData.state,TermCutRequest.progressData,kernelLocal]
  · simp [σ,KernelData.state,kernelMonomialRegisters]
  · intro i hi
    fin_cases i <;> simp_all [σ,KernelData.state,kernelMonomialRegisters]
  all_goals
    dsimp only [small,monomialLocalCapacity]
    exact List.le_sum_of_mem (by simp)

end NearQuarticWires.StageTuple
