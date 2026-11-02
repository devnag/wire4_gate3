import Proof.Quartic.StageCert.TableWord
import Proof.Quartic.StageCert.RecordCounts

set_option autoImplicit false

namespace NearQuarticWires.StageCertTests

open NearQuarticWires.StageCert
attribute [local instance] Classical.propDecidable

/-- `eq:testX`–`eq:testPhi`, paper/paper.tex:
one index selects an entire moment table over all original columns. -/
inductive TestKind (J : ℕ) where
  | population
  | digit (circuit : Fin 2) (pattern : Cycle.SignPattern 4) (position : Fin (J+1))
  | finalError (circuit : Fin 2) (pattern : Cycle.SignPattern 4)

/-- `sec:algorithm`, paper/paper.tex:
the exact test-table sequence is independent of the column. -/
noncomputable def testPlan (J : ℕ) (circuits : Finset (Fin 2)) : List (TestKind J) := by
  classical
  exact TestKind.population :: (List.finRange 2).flatMap fun j =>
    if j ∈ circuits then signPatterns.flatMap (fun σ =>
      if Cycle.kappa 4 σ ≠ 0 then
        (List.ofFn (fun r : Fin (J+1) => TestKind.digit j σ r)) ++ [TestKind.finalError j σ]
      else []) else []

/-- `eq:testX`–`eq:testPhi`, paper/paper.tex:
each table index names precisely the literal signed moment and threshold. -/
noncomputable def testRecord {N J : ℕ} (k : ℕ) (D : Walks.WalkData N 4 J) :
    TestKind J → MomentRecord
  | .population => populationRecord k D
  | .digit j σ r => digitRecord k D j σ r
  | .finalError j σ => finalRecord k D j σ

/-- `sec:algorithm`, paper/paper.tex:
the whole-table schedule is exactly the existing column record order. -/
theorem columnRecords_eq_testPlan {N J : ℕ} (k : ℕ) (D : Walks.WalkData N 4 J) :
    columnRecords k D = (testPlan J D.circuits).map (testRecord k D) := by
  classical
  simp only [columnRecords,testPlan,List.map_cons,testRecord,List.map_flatMap]
  congr 1
  apply congrArg (fun f : Fin 2 → List MomentRecord => (List.finRange 2).flatMap f)
  funext j
  by_cases hj : j ∈ D.circuits
  · simp only [hj,if_pos,List.map_flatMap]
    apply congrArg (fun f : Cycle.SignPattern 4 → List MomentRecord => signPatterns.flatMap f)
    funext σ
    split_ifs with hσ
    · rw [List.map_append,List.map_ofFn]
      rfl
    · rfl
  · simp only [hj,if_false,List.map_nil]

/-- `prop:time`, paper/paper.tex:
there are only polynomially many whole moment tables, rather than
one printed table for each individual walk. -/
theorem testPlan_length_le (J : ℕ) (circuits : Finset (Fin 2)) :
    (testPlan J circuits).length ≤ 1+512*(J+2) := by
  classical
  have hi (j : Fin 2) :
      ((if j ∈ circuits then signPatterns.flatMap (fun σ =>
        if Cycle.kappa 4 σ ≠ 0 then
          (List.ofFn (fun r : Fin (J+1) => TestKind.digit j σ r)) ++ [TestKind.finalError j σ]
        else []) else []) : List (TestKind J)).length ≤ 256*(J+2) := by
    split_ifs with hj
    · have h := bounded_flatMap_length signPatterns
        (fun σ => if Cycle.kappa 4 σ ≠ 0 then
          (List.ofFn (fun r : Fin (J+1) => TestKind.digit j σ r)) ++ [TestKind.finalError j σ]
          else []) (J+2) (by
            intro σ _
            split_ifs <;> simp only [List.length_append,List.length_ofFn,List.length_singleton,
              List.length_nil] <;> omega)
      have hl : signPatterns.length = 256 := by simp only [signPatterns,List.length_ofFn];norm_num
      rw [hl] at h
      exact h
    · simp
  have h := bounded_flatMap_length (List.finRange 2) _ (256*(J+2)) (fun j _ => hi j)
  simp only [testPlan,List.length_cons]
  simp only [List.length_finRange] at h
  omega

/-- `sec:algorithm`, paper/paper.tex:
one whole test table updates the current column flags by conjunction. -/
noncomputable def updateFlags {Z : ℕ} (flags : Fin Z → Bool) (table : Fin Z → MomentRecord) :
    Fin Z → Bool := fun z => flags z && recordPass (table z)

/-- `sec:algorithm`, paper/paper.tex:
streaming test-major conjunction equals the complete per-column strict test. -/
theorem foldFlags_all {Z : ℕ} (tables : List (Fin Z → MomentRecord))
    (flags : Fin Z → Bool) (z : Fin Z) :
    (tables.foldl updateFlags flags) z =
      (flags z && (tables.map (fun table => table z)).all recordPass) := by
  induction tables generalizing flags with
  | nil => simp
  | cons table tables ih =>
    simp only [List.foldl_cons,List.map_cons,List.all_cons]
    rw [ih]
    simp only [updateFlags,Bool.and_assoc]

/-- `sec:algorithm`, paper/paper.tex:
the final streaming flags equal the exact mathematical column certificates. -/
theorem foldFlags_certificate {N J Z : ℕ} (k : ℕ) (circuits : Finset (Fin 2))
    (columns : Fin Z → Walks.WalkData N 4 J)
    (hc : ∀ z, (columns z).circuits = circuits) (z : Fin Z) :
    (((testPlan J circuits).map (fun kind => fun z => testRecord k (columns z) kind)).foldl
      updateFlags (fun _ => true)) z =
      decide (Walks.ColumnCertificate (by norm_num) k (columns z)) := by
  rw [foldFlags_all]
  simp only [Bool.true_and,List.map_map,Function.comp_def]
  rw [←hc z,←columnRecords_eq_testPlan]
  exact columnPass_eq_certificate k (columns z)

end NearQuarticWires.StageCertTests
