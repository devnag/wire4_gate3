import Proof.Quartic.StageNativeKids.PriceTarget
import Proof.Quartic.Cells.ParametersPrintOriginalCost
import Proof.Quartic.StageNativeWidth.Polynomial

set_option autoImplicit false

namespace NearQuarticWires.StageNativeKidsPrice

/-- `prop:time`, paper/paper.tex: a uniform
polynomial bound uses a fixed coefficient and exponent for every request. -/
def Price {A : Type} (scale charge : A → ℕ) : Prop :=
  ∃ K e : ℕ, ∀ a, charge a ≤ K * scale a ^ e

namespace Price

variable {A B : Type} {s f g : A → ℕ}

/-- `prop:time`, paper/paper.tex: constants have
uniform polynomial cost, including at zero scale. -/
theorem constant (s : A → ℕ) (k : ℕ) : Price s (fun _ => k) :=
  ⟨k, 0, by simp⟩

/-- `prop:time`, paper/paper.tex: the structural
resource bounds itself. -/
theorem identity (s : A → ℕ) : Price s s := ⟨1, 1, by simp⟩

/-- `prop:time`, paper/paper.tex: pointwise
decreasing a charged quantity preserves a uniform polynomial bound. -/
theorem mono (h : Price s g) (hfg : ∀ a, f a ≤ g a) : Price s f := by
  obtain ⟨K, e, he⟩ := h
  exact ⟨K, e, fun a => (hfg a).trans (he a)⟩

/-- `prop:time`, paper/paper.tex: any directly
included structural resource has a uniform linear bound. -/
theorem of_le (h : ∀ a, f a ≤ s a) : Price s f := (identity s).mono h

/-- `prop:time`, paper/paper.tex: sequential
charges add with request-independent polynomial constants. -/
theorem add (hs : ∀ a, 1 ≤ s a) (hf : Price s f) (hg : Price s g) :
    Price s (fun a => f a + g a) := by
  obtain ⟨K, e, he⟩ := hf
  obtain ⟨L, d, hd⟩ := hg
  refine ⟨K+L, e+d, fun a => ?_⟩
  have h1 := (he a).trans (Nat.mul_le_mul_left K
    (Nat.pow_le_pow_right (hs a) (Nat.le_add_right e d)))
  have h2 := (hd a).trans (Nat.mul_le_mul_left L
    (Nat.pow_le_pow_right (hs a) (Nat.le_add_left d e)))
  nlinarith only [h1, h2]

/-- `prop:time`, paper/paper.tex: products of
physical resource charges retain a fixed polynomial exponent. -/
theorem mul (hf : Price s f) (hg : Price s g) :
    Price s (fun a => f a * g a) := by
  obtain ⟨K, e, he⟩ := hf
  obtain ⟨L, d, hd⟩ := hg
  refine ⟨K*L, e+d, fun a => ?_⟩
  calc
    _ ≤ (K*s a^e)*(L*s a^d) := Nat.mul_le_mul (he a) (hd a)
    _ = _ := by rw [pow_add]; ring

/-- `prop:time`, paper/paper.tex: fixed powers
of structural quantities retain uniform polynomial bounds. -/
theorem power (hf : Price s f) (k : ℕ) : Price s (fun a => f a ^ k) := by
  obtain ⟨K, e, he⟩ := hf
  refine ⟨K^k, e*k, fun a => ?_⟩
  calc
    _ ≤ (K*s a^e)^k := Nat.pow_le_pow_left (he a) k
    _ = _ := by rw [mul_pow, pow_mul]

/-- `prop:time`, paper/paper.tex: specializing
a uniform family to actual original-source requests changes no constants. -/
theorem comp (hf : Price s f) (q : B → A) :
    Price (fun b => s (q b)) (fun b => f (q b)) := by
  obtain ⟨K, e, he⟩ := hf
  exact ⟨K, e, fun b => he (q b)⟩

end Price

end NearQuarticWires.StageNativeKidsPrice
