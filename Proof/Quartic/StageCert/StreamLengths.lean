import Proof.Quartic.StageCert.FinishMachine

set_option autoImplicit false

namespace NearQuarticWires.StageCert
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces (listWord)
open NearCubicGates.Close.Cells (natWord_length)

/-- `prop:time`, paper/paper.tex: concatenating bounded
record words costs at most their number times the uniform word bound. -/
theorem flatMap_length_le {α : Type*} (xs : List α) (f : α → List Bool) (B : ℕ)
    (h : ∀ x ∈ xs, (f x).length ≤ B) : (xs.flatMap f).length ≤ xs.length*B := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons,List.length_append,List.length_cons]
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    nlinarith

/-- `prop:time`, paper/paper.tex: each serialized scalar
field has a linear bound in the common table width. -/
theorem scalarWord_length_le (r : CertTableRequest) (v : ℕ) (hv : v ∈ scalarFields r) :
    (natWord v).length ≤ 2*tableWidth r+1 := by
  rw [natWord_length]
  have h := scalar_height_lt_width r v hv
  omega

/-- `prop:time`, paper/paper.tex: all three fields of one
signed moment record have linear total word length. -/
theorem momentRecordWord_length_le (r : CertTableRequest) (rs : List MomentRecord)
    (hrs : rs ∈ r.columns) (t : MomentRecord) (ht : t ∈ rs) :
    (momentRecordWord t).length ≤ 6*tableWidth r+3 := by
  obtain ⟨h1,h2,h3⟩ := moment_fields_mem r rs hrs t ht
  have hs := scalarWord_length_le r _ h1
  have hm := scalarWord_length_le r _ h2
  have hb := scalarWord_length_le r _ h3
  simp only [momentRecordWord,NearCubicGates.Close.Interfaces.intWord,List.length_append]
  omega

/-- `prop:time`, paper/paper.tex: the complete signed
record block of one column has linear size in its actual number of tests. -/
theorem columnWord_length_le (r : CertTableRequest) (rs : List MomentRecord) (hrs : rs ∈ r.columns) :
    (listWord momentRecordWord rs).length ≤ 6*(rs.length+1)*(tableWidth r+1) := by
  have hh := scalarWord_length_le r _ (column_count_field r rs hrs)
  have ht := flatMap_length_le rs momentRecordWord _ (momentRecordWord_length_le r rs hrs)
  simp only [listWord,List.length_append]
  nlinarith

/-- `prop:time`, paper/paper.tex: the flattened sequence
of all column blocks has linear total size in the stream's true work count. -/
theorem columnBlocks_length_le (r : CertTableRequest) (columns : List (List MomentRecord))
    (hsub : ∀ rs ∈ columns, rs ∈ r.columns) :
    (columns.flatMap (listWord momentRecordWord)).length ≤
      6*streamWork columns*(tableWidth r+1) := by
  induction columns with
  | nil => simp [streamWork]
  | cons rs columns ih =>
    have hh := columnWord_length_le r rs (hsub rs (by simp))
    have ht := ih (fun t ht => hsub t (by simp [ht]))
    simp only [List.flatMap_cons,List.length_append,streamWork]
    nlinarith

/-- `prop:time`, paper/paper.tex: the nested table record
encoding contains no multiplicative dependence on its total bit length. -/
theorem columnsWord_length_le (r : CertTableRequest) :
    (listWord (listWord momentRecordWord) r.columns).length ≤
      6*(streamWork r.columns+1)*(tableWidth r+1) := by
  have hh := scalarWord_length_le r r.columns.length (by simp [scalarFields])
  have ht := columnBlocks_length_le r r.columns (fun _ h => h)
  simp only [listWord,List.length_append]
  nlinarith

/-- `prop:time`, paper/paper.tex: the full physical input
length is linear in the payload and true moment-record count, up to the
common scalar height. -/
theorem certTableWord_length_le (r : CertTableRequest) :
    (certTableWord r).length ≤
      20*(r.payload.length+streamWork r.columns+tableWidth r+1)*(tableWidth r+1) := by
  have hh : (natWord (tableWidth r)).length ≤ 2*tableWidth r+3 := by
    rw [natWord_length]
    have h := Nat.log_le_self 2 (tableWidth r)
    unfold natBitLength
    omega
  have hp := scalarWord_length_le r r.payload.length (by simp [scalarFields])
  have hf := scalarWord_length_le r (if r.doAppend then 1 else 0) (by simp [scalarFields])
  have hc := columnsWord_length_le r
  simp only [certTableWord,List.length_append]
  nlinarith

end NearQuarticWires.StageCert
