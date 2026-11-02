import Proof.Quartic.StageCert.Records
import Proof.Quartic.StageCert.ColumnStream

set_option autoImplicit false

namespace NearQuarticWires.StageCert

/-- `prop:time`, paper/paper.tex: the length of a finite
flattened record family is bounded by its exact index count times its
uniform block length. -/
theorem bounded_flatMap_length {α β : Type*} (xs : List α) (f : α→List β) (B : ℕ)
    (h : ∀ x∈xs,(f x).length≤B) : (xs.flatMap f).length≤xs.length*B := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [List.flatMap_cons,List.length_append,List.length_cons]
    nlinarith

/-- `eq:testX`–`eq:testPhi` and `prop:time`, paper/paper.tex: only two circuit roles and 256 actual sign patterns
are scanned; each has `J+1` digit records and one final-error record. -/
theorem columnRecords_length_le {N J : ℕ} (k : ℕ) (D : Walks.WalkData N 4 J) :
    (columnRecords k D).length≤1+512*(J+2) := by
  classical
  have hinner (j : Fin 2) :
      ((if j∈D.circuits then signPatterns.flatMap (fun σ =>
        if Cycle.kappa 4 σ≠0 then List.ofFn (digitRecord k D j σ)++[finalRecord k D j σ]
        else []) else []) : List MomentRecord).length≤256*(J+2) := by
    split_ifs with hj
    · have h := bounded_flatMap_length signPatterns
        (fun σ => if Cycle.kappa 4 σ≠0 then List.ofFn (digitRecord k D j σ)++[finalRecord k D j σ] else [])
        (J+2) (by intro σ hσ; split_ifs <;> simp)
      have hlen : signPatterns.length=256 := by simp only [signPatterns,List.length_ofFn]; norm_num
      rw [hlen] at h
      exact h
    · simp
  have h := bounded_flatMap_length (List.finRange 2)
    (fun j => if j∈D.circuits then signPatterns.flatMap (fun σ =>
      if Cycle.kappa 4 σ≠0 then List.ofFn (digitRecord k D j σ)++[finalRecord k D j σ]
      else []) else []) (256*(J+2)) (fun j _ => hinner j)
  simp only [columnRecords,List.length_cons]
  simp only [List.length_finRange] at h
  omega

/-- `prop:time`, paper/paper.tex: the physical scan work
includes one header for every original column and all its test records. -/
theorem streamWork_le (columns : List (List MomentRecord)) (B : ℕ)
    (h : ∀ rs∈columns,rs.length≤B) : streamWork columns≤columns.length*(B+1) := by
  induction columns with
  | nil => simp [streamWork]
  | cons rs columns ih =>
    have hh := h rs (by simp)
    have ht := ih (fun t ht => h t (by simp [ht]))
    simp only [streamWork,List.length_cons]
    nlinarith

end NearQuarticWires.StageCert
