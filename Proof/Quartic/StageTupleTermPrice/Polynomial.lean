import Proof.Quartic.StageTupleTermPrice.Data

set_option autoImplicit false

namespace NearQuarticWires.StageTupleTermPrice

/-- `prop:time`, paper/paper.tex: fixed
structural polynomials price actual local quantities without changing
the separate original-child census factor. -/
def Price {I : Type} (small : I→ℕ) (f : I→ℕ) : Prop :=
  ∃C E : ℕ,∀j,f j≤ C*(small j)^E

theorem Price.mono {I : Type} {s f g : I→ℕ} (hg : Price s g)
    (h : ∀j,f j≤ g j) : Price s f := by
  obtain ⟨C,E,hg⟩:=hg
  exact ⟨C,E,fun j=>(h j).trans (hg j)⟩

theorem Price.constant {I : Type} (s : I→ℕ) (c : ℕ) : Price s (fun _=> c) := by
  exact ⟨c,0,by intro j;simp⟩

theorem Price.scalar {I : Type} {s f : I→ℕ} (h : ∀j,f j≤ s j) : Price s f := by
  exact ⟨1,1,by simpa using h⟩

theorem Price.add {I : Type} {s f g : I→ℕ} (hs : ∀j,1≤ s j)
    (hf : Price s f) (hg : Price s g) : Price s (fun j=> f j+g j) := by
  obtain ⟨C,E,hf⟩:=hf
  obtain ⟨K,L,hg⟩:=hg
  refine ⟨C+K,E+L,fun j=>?_⟩
  have he:=Nat.pow_le_pow_right (hs j) (show E≤ E+L by omega)
  have hl:=Nat.pow_le_pow_right (hs j) (show L≤ E+L by omega)
  have h1:=(hf j).trans (Nat.mul_le_mul_left C he)
  have h2:=(hg j).trans (Nat.mul_le_mul_left K hl)
  nlinarith only [h1,h2]

theorem Price.mul {I : Type} {s f g : I→ℕ} (hf : Price s f) (hg : Price s g) :
    Price s (fun j=> f j*g j) := by
  obtain ⟨C,E,hf⟩:=hf
  obtain ⟨K,L,hg⟩:=hg
  refine ⟨C*K,E+L,fun j=>?_⟩
  calc
    _≤(C*(s j)^E)*(K*(s j)^L) := Nat.mul_le_mul (hf j) (hg j)
    _=_ := by rw [pow_add];ring

theorem Price.pow {I : Type} {s f : I→ℕ} (hf : Price s f) (p : ℕ) :
    Price s (fun j=>(f j)^p) := by
  obtain ⟨C,E,hf⟩:=hf
  refine ⟨C^p,E*p,fun j=>?_⟩
  calc
    _≤(C*(s j)^E)^p := Nat.pow_le_pow_left (hf j) _
    _=_ := by rw [mul_pow,←pow_mul]

theorem Price.comp {I J : Type} {s f : I→ℕ} (hf : Price s f) (g : J→I) :
    Price (fun j=> s (g j)) (fun j=> f (g j)) := by
  obtain ⟨C,E,hf⟩:=hf
  exact ⟨C,E,fun j=> hf (g j)⟩

theorem Case.small_pos (j : Case) : 1≤ j.small := by have h:=j.small_bounds.1;omega

end NearQuarticWires.StageTupleTermPrice
