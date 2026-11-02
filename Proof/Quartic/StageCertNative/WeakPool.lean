import Proof.Quartic.StageCertNative.TupleJoin
import Proof.Quartic.StageCertNative.CachedCount
import Proof.Quartic.StageCertificateControl.BatchedMachine
import Proof.Quartic.StageCertificateControl.ExtendedBank

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open StageCertificateControl

/-- `lem:print`, paper/paper.tex: the actual
whole-test family enumerates precisely N² population terms or N⁸
moment terms, each at the original shared cached source. -/
noncomputable def termFamily {B1 B2 : ℕ} (r : IndexedRequest B1 B2) :
    StagePrint.PoolFamily (TermJob B1 B2) TermJob.word where
  count:=termCount r
  source:=cachedSourceWord r
  request:=fun i=>⟨r,i⟩
  indexed:=fun _=>rfl

noncomputable def wholeWeakWord {B1 B2 : ℕ} (r : IndexedRequest B1 B2) : List Bool :=
  (List.ofFn (fun i : Fin (termCount r)=>termWeakWord ⟨r,i⟩)).flatten

/-- `lem:print`, paper/paper.tex: the actual
counted cache order is exactly original low-first term order. -/
theorem wholeWeakWord_eq_range {B1 B2 : ℕ} (r : IndexedRequest B1 B2) :
    wholeWeakWord r=(List.range (termCount r)).flatMap ((termFamily r).caches termWeakWord) := by
  have he : List.ofFn (fun i : Fin (termCount r)=>termWeakWord ⟨r,i⟩)=
      (List.range (termCount r)).map ((termFamily r).caches termWeakWord) := by
    apply List.ext_getElem
    · simp
    · intro i hi hi'
      simp only [List.length_ofFn] at hi
      simp only [List.getElem_ofFn,List.getElem_map,List.getElem_range]
      simp only [StagePrint.PoolFamily.caches,termFamily,hi,dif_pos]
  have hh:=congrArg List.flatten he
  simpa only [wholeWeakWord,List.flatten_eq_flatMap,List.flatMap_map,Function.comp_def,id_eq] using hh

noncomputable def wholeWeakSourceWord {B1 B2 : ℕ} (r : IndexedRequest B1 B2) : List Bool :=
  cachedSourceWord r++natWord (termCount r)++wholeWeakWord r

section
variable {B1 B2 : ℕ} {termBudget : TermJob B1 B2→ℕ}
variable (termProducer : WordFunction (TermJob B1 B2) TermJob.word
  (fun r=>frame (termWeakWord r)) termBudget)

noncomputable def weakPoolBudget (r : IndexedRequest B1 B2) : ℕ :=
  batchedMachineBudget (termFamily r) termWeakWord termBudget (cachedCountBudget r)

/-- `lem:print` and `prop:time`, paper/paper.tex: one real counted loop computes every per-term signed
stream and concatenates it once, retaining the actual source and count.
No global equality square or padded field census replaces the term loop. -/
noncomputable def weakPoolWordFunction :
    WordFunction (IndexedRequest B1 B2) cachedSourceWord
      (fun r=>frame (wholeWeakSourceWord r)) (weakPoolBudget (termBudget:=termBudget)) := by
  let counter:=cachedCountWordFunction B1 B2
  let provider:=extendedBankWordFunction termProducer counter.program.tapeCount
  have hq : counter.program.tapeCount≤provider.program.tapeCount := by
    change counter.program.tapeCount≤termProducer.program.tapeCount+counter.program.tapeCount
    omega
  let f:=batchedTablesWordFunction counter provider hq termFamily (fun _=>rfl) (fun _=>rfl)
  refine ⟨f.program,?_⟩
  intro r
  have hh : flattenedPoolWord (termFamily r).source ((termFamily r).caches termWeakWord)
      (termFamily r).count=wholeWeakSourceWord r := by
    unfold flattenedPoolWord wholeWeakSourceWord
    rw [wholeWeakWord_eq_range]
    rfl
  simpa only [hh,weakPoolBudget] using f.realizes r

noncomputable def originalWeakPoolBudget (r : IndexedRequest B1 B2) : ℕ :=
  4*cachedSourceBudget r+4*weakPoolBudget (termBudget:=termBudget) r+12

/-- `lem:print`, paper/paper.tex: all terms of
the whole original test are computed from BASE alone, including the
one-time actual context and count acquisition. -/
noncomputable def originalWeakPoolWordFunction :
    WordFunction (IndexedRequest B1 B2) IndexedRequest.baseWord
      (fun r=>frame (wholeWeakSourceWord r)) (originalWeakPoolBudget (termBudget:=termBudget)) :=
  Program.WordFunction.pipe (cachedSourceWordFunction B1 B2) (weakPoolWordFunction termProducer)

end

end NearQuarticWires.StageCertNative
