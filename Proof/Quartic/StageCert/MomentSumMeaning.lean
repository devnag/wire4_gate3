import Proof.Quartic.StageCert.MomentTermMeaning

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires
open NearCubicGates.Close.Tabulator

/-- `eq:testE` and `lem:print`, paper/paper.tex: summing exactly the original low-first source terms
gives the complete signed digit record on every original column. -/
theorem MomentRequest.digit_term_sum {B1 B2 : ℕ} (r : MomentRequest B1 B2)
    (j : Fin 2) (code : Fin 256) (row : Fin (r.selected.1.J-1+1))
    (ht : r.test=.digit j code row) (z : Fin (2^(r.call.n-r.selected.1.k))) :
    (∑ i : Fin (momentTermCount r.selected.1.N r.test), (r.withIndex i).termValue z)=
      (digitRecord r.selected.1.k (Builder.columnData r.call r.rules r.witness z)
        j (StageCertTests.patternOfCode code.val) row).1 := by
  classical
  have hcount : momentTermCount r.selected.1.N r.test=r.selected.1.N^8 := by rw [ht]; rfl
  let f : Cycle.Walk r.rules.seedParameters.N 4→ℤ := fun walk=>
    (StagePrint.callMomentFormula r.call r.rules r.retainedWitness walk j
      (StagePrint.callDigitWeights r.call r.rules r.retainedWitness j row)
      (StageCertTests.patternOfCode code.val)).eval
      (boolPoint (Cells.walkAtomPoint (Builder.star r.call r.rules) (by decide : 0<4)
        (StagePrint.callPatterns r.call r.rules walk) (StagePrint.callAtoms r.call)
        (Builder.center r.call r.rules r.retainedWitness z)))
  calc
    _=∑ i : Fin (momentTermCount r.selected.1.N r.test), f (r.walkTermEquiv hcount i) := by
      apply Finset.sum_congr rfl
      intro i _
      have hv := (r.withIndex i).digit_term_value j code row ht z
      change (r.withIndex i).termValue z=f ((r.withIndex i).walk) at hv
      rw [r.walkTermEquiv_eq hcount i] at hv
      exact hv
    _=∑ walk, f walk := (r.walkTermEquiv hcount).sum_comp f
    _=(digitRecord r.selected.1.k (Builder.columnData r.call r.rules r.retainedWitness z)
        j (StageCertTests.patternOfCode code.val) row).1 :=
      StagePrint.callDigitMoment_sum r.call r.rules r.retainedWitness z j _ row
    _=_ := by rw [r.retained_columnData_eq]

/-- `eq:testPhi` and `lem:print`, paper/paper.tex: the whole exact source sum retains every signed
final-error offset and equals the original column's literal record. -/
theorem MomentRequest.final_term_sum {B1 B2 : ℕ} (r : MomentRequest B1 B2)
    (j : Fin 2) (code : Fin 256) (ht : r.test=.finalError j code)
    (z : Fin (2^(r.call.n-r.selected.1.k))) :
    (∑ i : Fin (momentTermCount r.selected.1.N r.test), (r.withIndex i).termValue z)=
      (finalRecord r.selected.1.k (Builder.columnData r.call r.rules r.witness z)
        j (StageCertTests.patternOfCode code.val)).1 := by
  classical
  have hcount : momentTermCount r.selected.1.N r.test=r.selected.1.N^8 := by rw [ht]; rfl
  let f : Cycle.Walk r.rules.seedParameters.N 4→ℤ := fun walk=>
    (StagePrint.callMomentFormula r.call r.rules r.retainedWitness walk j
      (StagePrint.callFinalWeights r.call r.selected.1 r.retainedWitness j)
      (StageCertTests.patternOfCode code.val)).eval
      (boolPoint (Cells.walkAtomPoint (Builder.star r.call r.rules) (by decide : 0<4)
        (StagePrint.callPatterns r.call r.rules walk) (StagePrint.callAtoms r.call)
        (Builder.center r.call r.rules r.retainedWitness z)))
  calc
    _=∑ i : Fin (momentTermCount r.selected.1.N r.test), f (r.walkTermEquiv hcount i) := by
      apply Finset.sum_congr rfl
      intro i _
      have hv := (r.withIndex i).final_term_value j code ht z
      change (r.withIndex i).termValue z=f ((r.withIndex i).walk) at hv
      rw [r.walkTermEquiv_eq hcount i] at hv
      exact hv
    _=∑ walk, f walk := (r.walkTermEquiv hcount).sum_comp f
    _=(finalRecord r.selected.1.k (Builder.columnData r.call r.rules r.retainedWitness z)
        j (StageCertTests.patternOfCode code.val)).1 :=
      StagePrint.callFinalMoment_sum r.call r.rules r.retainedWitness z j _
    _=_ := by rw [r.retained_columnData_eq]

/-- `eq:testX` and `lem:print`, paper/paper.tex: the N² population terms sum over every original
cell exactly once and vanish on structurally excluded cells. -/
theorem MomentRequest.population_term_sum {B1 B2 : ℕ} (r : MomentRequest B1 B2)
    (ht : r.test=.population) (z : Fin (2^(r.call.n-r.selected.1.k))) :
    (∑ i : Fin (momentTermCount r.selected.1.N r.test), (r.withIndex i).termValue z)=
      (populationRecord r.selected.1.k (Builder.columnData r.call r.rules r.witness z)).1 := by
  classical
  let D := Builder.columnData r.call r.rules r.witness z
  let f : Sampler.Cell r.rules.seedParameters.N→ℤ := fun q=>
    (if D.structural q then (1:ℤ) else 0)*(D.X q : ℤ)^(2*r.selected.1.k)
  calc
    _=∑ i : Fin (momentTermCount r.selected.1.N r.test), f (r.cellTermEquiv ht i) := by
      apply Finset.sum_congr rfl
      intro i _
      have hv := (r.withIndex i).population_term_value ht z
      change (r.withIndex i).termValue z=f (Cycle.edge (by decide : 0<4) (r.withIndex i).walk 0) at hv
      exact hv.trans (congrArg f (r.population_edge_eq ht i))
    _=∑ q, f q := (r.cellTermEquiv ht).sum_comp f
    _=∑ q : Walks.StructuralPoint D.structural, f q.val :=
      StagePrint.sum_eq_structural (fun q=>D.structural q=true) f (by
        intro q hq
        cases hb : D.structural q
        · simp only [f,hb,Bool.false_eq_true,if_false,zero_mul]
        · exact (hq hb).elim)
    _=(populationRecord r.selected.1.k D).1 := by
      unfold populationRecord Walks.momentSum
      apply Finset.sum_congr rfl
      intro q _
      simp only [f,q.property,if_true,one_mul]

/-- `eq:testX`–`eq:testPhi` and `lem:print`, paper/paper.tex: the actual source term sum
equals the exact original whole-test signed table entry on every
column, with no witness or certification premise. -/
theorem MomentRequest.term_sum_eq_actualTestTable {B1 B2 : ℕ} (r : MomentRequest B1 B2)
    (z : Fin (2^(r.call.n-r.selected.1.k))) :
    (∑ i : Fin (momentTermCount r.selected.1.N r.test), (r.withIndex i).termValue z)=
      (StageCertTests.actualTestTable r.call r.rules r.witness r.test.kind z).1 := by
  cases r with
  | mk c p hd w test index =>
    cases test with
    | population =>
      exact (⟨c,p,hd,w,.population,index⟩ : MomentRequest B1 B2).population_term_sum rfl z
    | digit j code row =>
      exact (⟨c,p,hd,w,.digit j code row,index⟩ : MomentRequest B1 B2).digit_term_sum j code row rfl z
    | finalError j code =>
      exact (⟨c,p,hd,w,.finalError j code,index⟩ : MomentRequest B1 B2).final_term_sum j code rfl z

end NearQuarticWires.StageCert.Tokens
