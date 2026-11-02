import Proof.Quartic.StageCertTests.TestPlan

set_option autoImplicit false

namespace NearQuarticWires.StageCertTests

open NearCubicGates.Close.Interfaces
attribute [local instance] Classical.propDecidable

/-- `sec:algorithm`, paper/paper.tex:
the actual call's whole-table schedule depends only on its active
circuits and selected rate-chain length, not on the column or witness. -/
noncomputable def actualTestPlan (c : Call) (p : Cells.Parameters) : List (TestKind (p.J-1)) :=
  testPlan (p.J-1) (Builder.circuitSet c)

/-- `sec:algorithm`, paper/paper.tex:
each selected test yields one whole table over all exact original columns. -/
noncomputable def actualTestTable (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (w : List Bool)
    (kind : TestKind (p.J-1)) (z : Fin (2^(c.n-p.k))) : StageCert.MomentRecord :=
  testRecord p.k (Builder.columnData c hs w z) kind

/-- `sec:algorithm`, paper/paper.tex:
the complete streaming conjunction is exactly the literal certificate
bitmap required by the machine stage. -/
theorem actualFlags_eq_certifiedBits (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (w : List Bool) :
    List.ofFn (((actualTestPlan c p).map (actualTestTable c hs w)).foldl updateFlags (fun _ => true)) =
      Program.certifiedBits (Builder.cellCall c hs w) := by
  apply congrArg List.ofFn
  funext z
  have h := foldFlags_certificate p.k (Builder.circuitSet c)
    (Builder.columnData c hs w) (fun _ => rfl) z
  simp only [Algorithm.CellCall.certifiedColumns,Finset.mem_filter,Finset.mem_univ,
    true_and,Algorithm.CellCall.Certified]
  change ((testPlan (p.J-1) (Builder.circuitSet c)).map
    (fun kind z => testRecord p.k (Builder.columnData c hs w z) kind)).foldl
      updateFlags (fun _ => true) z =
        decide (Walks.ColumnCertificate (by norm_num) p.k (Builder.columnData c hs w z))
  exact h

/-- `prop:time`, paper/paper.tex:
the actual whole-table schedule has polynomial size in the selected chain. -/
theorem actualTestPlan_length_le (c : Call) (p : Cells.Parameters) (hJ : 1 ≤ p.J) :
    (actualTestPlan c p).length ≤ 1+512*(p.J+1) := by
  have h := testPlan_length_le (p.J-1) (Builder.circuitSet c)
  unfold actualTestPlan
  exact h.trans (by omega)

/-- `eq:testX`–`eq:testPhi`, paper/paper.tex:
the strict threshold for a whole moment table is one selected scalar,
independent of the original column or witness. -/
def actualTestThreshold (p : Cells.Parameters) : TestKind (p.J-1) → ℕ
  | .population => (p.Xmax+1)^(2*p.k)
  | .digit _ _ _ => p.hE^(8*p.k)
  | .finalError _ _ => p.Lambda^(8*p.k)

/-- `eq:testX`–`eq:testPhi`, paper/paper.tex:
the streamed scalar threshold is exactly the threshold in every
corresponding literal column record. -/
theorem actualTestTable_threshold (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (w : List Bool)
    (kind : TestKind (p.J-1)) (z : Fin (2^(c.n-p.k))) :
    (actualTestTable c hs w kind z).2 = actualTestThreshold p kind := by
  cases kind <;> simp only [actualTestTable,testRecord,actualTestThreshold,
    StageCert.populationRecord,StageCert.digitRecord,StageCert.finalRecord,Builder.columnData]
  all_goals (congr 1;omega)

end NearQuarticWires.StageCertTests
