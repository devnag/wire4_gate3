import Proof.Quartic.StageTupleTermPrice.Polynomial

set_option autoImplicit false

namespace NearQuarticWires.StageTupleTermPrice

/-- `prop:time`, paper/paper.tex: a
separate census factor is multiplied only by structural polynomials,
so its support exponent is preserved throughout actual composition. -/
def WeightedPrice {I : Type} (small weight f : I→ℕ) : Prop :=
  ∃C E : ℕ,∀j,f j≤C*(small j)^E*weight j

theorem WeightedPrice.mono {I : Type} {s w f g : I→ℕ} (hg : WeightedPrice s w g)
    (h : ∀j,f j≤g j) : WeightedPrice s w f := by
  obtain ⟨C,E,hg⟩:=hg
  exact ⟨C,E,fun j=>(h j).trans (hg j)⟩

theorem WeightedPrice.of_price {I : Type} {s w f : I→ℕ} (hw : ∀j,1≤w j)
    (hf : Price s f) : WeightedPrice s w f := by
  obtain ⟨C,E,hf⟩:=hf
  exact ⟨C,E,fun j=>(hf j).trans (Nat.le_mul_of_pos_right _ (by have h:=hw j;omega))⟩

theorem WeightedPrice.add {I : Type} {s w f g : I→ℕ} (hs : ∀j,1≤ s j)
    (hf : WeightedPrice s w f) (hg : WeightedPrice s w g) : WeightedPrice s w (fun j=>f j+g j) := by
  obtain ⟨C,E,hf⟩:=hf
  obtain ⟨K,L,hg⟩:=hg
  refine ⟨C+K,E+L,fun j=>?_⟩
  have he:=Nat.pow_le_pow_right (hs j) (show E≤E+L by omega)
  have hl:=Nat.pow_le_pow_right (hs j) (show L≤E+L by omega)
  have h1:=(hf j).trans (Nat.mul_le_mul_right (w j) (Nat.mul_le_mul_left C he))
  have h2:=(hg j).trans (Nat.mul_le_mul_right (w j) (Nat.mul_le_mul_left K hl))
  nlinarith only [h1,h2]

theorem WeightedPrice.mul_small {I : Type} {s w f g : I→ℕ}
    (hf : Price s f) (hg : WeightedPrice s w g) : WeightedPrice s w (fun j=>f j*g j) := by
  obtain ⟨C,E,hf⟩:=hf
  obtain ⟨K,L,hg⟩:=hg
  refine ⟨C*K,E+L,fun j=>?_⟩
  calc
    _≤(C*(s j)^E)*(K*(s j)^L*w j) := Nat.mul_le_mul (hf j) (hg j)
    _=_ := by rw [pow_add];ring

end NearQuarticWires.StageTupleTermPrice
