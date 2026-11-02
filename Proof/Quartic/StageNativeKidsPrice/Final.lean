import Proof.Quartic.StageNativeKidsPrice.RowClocks

set_option autoImplicit false

namespace NearQuarticWires.StageNativeKidsPrice

open StageNativeKids StagePrint StageTuple

/-- `prop:time`, paper/paper.tex: both
actual original-source count clocks and every actual original-child row
pipeline have one fixed polynomial price in the literal request length,
original arity and unchanged sharp original child cap. All source
selection, compilation, counting, signed pullback, copying and framing
are included in the concrete clocks; no extra input premise is required. -/
theorem originalSourcePrice : ∃ K e : ℕ, StageNativeKids.OriginalSourcePrice K e := by
  obtain ⟨Kc, ec, hc⟩ := count_price
  obtain ⟨Kr, er, hr⟩ := row_price
  have countBound (a : SourceCase) :
      indexedOriginalCountBudget a.source ≤ (Kc+Kr)*a.scale^(ec+er) := by
    calc
      _ ≤ Kc*a.scale^ec := hc a
      _ ≤ Kc*a.scale^(ec+er) := Nat.mul_le_mul_left Kc
        (Nat.pow_le_pow_right (scale_pos a) (Nat.le_add_right ec er))
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.le_add_right Kc Kr)
  have rowBound (a : RowCase) : a.pipeline.budget ≤ (Kc+Kr)*a.scale^(ec+er) := by
    calc
      _ ≤ Kr*a.scale^er := hr a
      _ ≤ Kr*a.scale^(ec+er) := Nat.mul_le_mul_left Kr
        (Nat.pow_le_pow_right (row_scale_pos a) (Nat.le_add_left er ec))
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.le_add_left Kr Kc)
  refine ⟨Kc+Kr, ec+er, ?_⟩
  intro r
  exact ⟨(fun h => countBound ⟨r, false, h⟩),
    (fun h => countBound ⟨r, true, h⟩),
    (fun h j => rowBound ⟨⟨r, false, h⟩, j⟩),
    (fun h j => rowBound ⟨⟨r, true, h⟩, j⟩)⟩

end NearQuarticWires.StageNativeKidsPrice
