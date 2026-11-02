import Proof.Quartic.StageCert.ColumnMachine

set_option autoImplicit false

namespace NearQuarticWires.StageCert
open NearCubicWires

/-- `prop:time`, paper/paper.tex: a running maximum retains
its initial lower bound. -/
theorem le_foldMax (l : List ℕ) (b : ℕ) : b ≤ l.foldl max b := by
  induction l generalizing b with
  | nil => exact le_rfl
  | cons a l ih => exact (le_max_left b a).trans (ih _)

/-- `prop:time`, paper/paper.tex: every scalar height is
bounded by the exact running maximum of the serialized fields. -/
theorem mem_le_foldMax (l : List ℕ) (b a : ℕ) (ha : a ∈ l) : a ≤ l.foldl max b := by
  induction l generalizing b with
  | nil => simp at ha
  | cons c l ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact (le_max_right _ _).trans (le_foldMax l _)
    · exact ih _ ha

/-- `prop:time`, paper/paper.tex: every scalar field of the
certificate stream fits the declared arithmetic width with two spare bits. -/
theorem scalar_height_lt_width (r : CertTableRequest) (v : ℕ) (hv : v ∈ scalarFields r) :
    natBitLength v+2 ≤ tableWidth r := by
  have h := mem_le_foldMax ((scalarFields r).map natBitLength) 0 (natBitLength v)
    (List.mem_map.mpr ⟨v,hv,rfl⟩)
  unfold tableWidth
  omega

/-- `sec:algorithm`, paper/paper.tex: each column count is an
actual field of the shared certificate stream. -/
theorem column_count_field (r : CertTableRequest) (rs : List MomentRecord) (hrs : rs ∈ r.columns) :
    rs.length ∈ scalarFields r := by
  simp only [scalarFields, List.mem_cons]
  right; right; right
  exact List.mem_flatMap.mpr ⟨rs,hrs,List.mem_cons_self ..⟩

/-- `sec:algorithm`, paper/paper.tex: every signed-record field is
represented in the stream's width census. -/
theorem moment_fields_mem (r : CertTableRequest) (rs : List MomentRecord) (hrs : rs ∈ r.columns)
    (t : MomentRecord) (ht : t ∈ rs) :
    (if t.1<0 then 1 else 0) ∈ scalarFields r ∧ t.1.natAbs ∈ scalarFields r ∧ t.2 ∈ scalarFields r := by
  have hmem : ∀ v ∈ [if t.1<0 then 1 else 0, t.1.natAbs, t.2], v ∈ scalarFields r := by
    intro v hv
    simp only [scalarFields, List.mem_cons]
    right; right; right
    refine List.mem_flatMap.mpr ⟨rs, hrs, List.mem_cons.mpr (Or.inr ?_)⟩
    exact List.mem_flatMap.mpr ⟨t,ht,hv⟩
  exact ⟨hmem _ (by simp), hmem _ (by simp), hmem _ (by simp)⟩

/-- `sec:algorithm`, paper/paper.tex: the concrete column requests
of the global stream satisfy all guards of the physical column reducer. -/
def tableColumnRequest (r : CertTableRequest) (rs : List MomentRecord) (hrs : rs ∈ r.columns) : ColumnRequest where
  width := tableWidth r
  tests := rs
  countFits := (Nat.le_add_right _ 2).trans (scalar_height_lt_width r _ (column_count_field r rs hrs))
  fieldsFit := by
    intro t ht
    obtain ⟨h1,h2,h3⟩ := moment_fields_mem r rs hrs t ht
    exact ⟨(Nat.le_add_right _ 2).trans (scalar_height_lt_width r _ h1),
      (Nat.le_add_right _ 2).trans (scalar_height_lt_width r _ h2),
      (Nat.le_add_right _ 2).trans (scalar_height_lt_width r _ h3)⟩

end NearQuarticWires.StageCert
