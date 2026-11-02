import Proof.Gates.ResidueCounts
import Proof.Gates.CountingCore
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option autoImplicit false

namespace NearQuarticWires.Walks

open scoped BigOperators

variable {W Forms : Type*} [Fintype W] [Fintype Forms]

/-- Paper `lem:residue`, paper/paper.tex: the literal integer printed value
`Pi(z)`, with arbitrary SIGNED scaled walk weights and the exact mask polynomial. -/
def residuePolynomial (g polyMask : W → ℤ) (p e : ℕ)
    (scores : W → Forms → ℤ) (rho : Forms → ℤ) : ℤ :=
  ∑ w, g w * polyMask w * NearCubicGates.ResidueCounts.liftedIndicator p e (scores w) rho

/-- Paper `lem:residue`, paper/paper.tex: the signed integer residue count
`N(z)` of the joint digits and walk sums on the retained walks. -/
noncomputable def residueCount (g mask : W → ℤ) (p : ℕ)
    (scores : W → Forms → ℤ) (rho : Forms → ℤ) : ℤ := by
  classical
  exact ∑ w, if ∀ i, scores w i ≡ rho i [ZMOD (p : ℤ)] then g w * mask w else 0

/-- Paper `lem:residue`, paper/paper.tex: Fermat and the literal Beigel--Tarui
polynomial remain exact modulo `p^e` after multiplication by SIGNED integer
weights and the independently certified exact mask. -/
theorem residuePolynomial_modEq_count (g polyMask mask : W → ℤ)
    (hmask : ∀ w, polyMask w = mask w) (p : ℕ) (hp : Nat.Prime p)
    (e : ℕ) (he : 1 ≤ e) (scores : W → Forms → ℤ) (rho : Forms → ℤ) :
    residuePolynomial g polyMask p e scores rho ≡ residueCount g mask p scores rho
      [ZMOD (p : ℤ) ^ e] := by
  classical
  apply NearCubicGates.ResidueCounts.sum_modEq
  intro w
  have hf := NearCubicGates.ResidueCounts.liftedIndicator_modEq p hp e he (scores w) rho
  have h := (Int.ModEq.refl (g w * mask w)).mul hf
  rw [hmask w]
  by_cases hg : ∀ i, scores w i ≡ rho i [ZMOD (p : ℤ)]
  · simpa only [if_pos hg, mul_one] using h
  · simpa only [if_neg hg, mul_zero] using h

/-- Paper `lem:residue`, paper/paper.tex: Boolean masking bounds the absolute
SIGNED residue count by the full absolute scaled walk mass. -/
theorem residueCount_abs_le (g mask : W → ℤ) (hmask : ∀ w, |mask w| ≤ 1)
    (p : ℕ) (scores : W → Forms → ℤ) (rho : Forms → ℤ) :
    |residueCount g mask p scores rho| ≤ ∑ w, |g w| := by
  classical
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro w _
  by_cases hg : ∀ i, scores w i ≡ rho i [ZMOD (p : ℤ)]
  · simp only [if_pos hg, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (hmask w)
  · simp only [if_neg hg, abs_zero]
    exact abs_nonneg _

/-- Paper `lem:residue`, paper/paper.tex: the integer representative of the
centered half-open interval `(-q/2,q/2]`, valid for odd and even moduli. -/
def centeredResidue (q value : ℤ) : ℤ :=
  (value + (q - 1) / 2) % q - (q - 1) / 2

/-- Paper `lem:residue`, paper/paper.tex: exact centered decoding, including
signed answers and the specified positive endpoint convention. -/
theorem centeredResidue_eq (q value answer : ℤ) (_hq : 0 < q)
    (hmod : value ≡ answer [ZMOD q])
    (hlow : -q < 2 * answer) (hup : 2 * answer ≤ q) :
    centeredResidue q value = answer := by
  have hrange : 0 ≤ answer + (q - 1) / 2 ∧ answer + (q - 1) / 2 < q := by omega
  have hshift : (value + (q - 1) / 2) % q = (answer + (q - 1) / 2) % q := by
    exact (hmod.add (Int.ModEq.refl ((q - 1) / 2))).eq
  unfold centeredResidue
  rw [hshift, Int.emod_eq_of_lt hrange.1 hrange.2]
  omega

/-- Paper `lem:residue`, paper/paper.tex: complete signed residue recovery.
The guard is the paper's `p^e > 2 * 2^S * sum |c(w)|`, expressed directly
in terms of the actual integer weights `g(w)=2^S*c(w)`. -/
theorem signed_residue_recovery (g polyMask mask : W → ℤ)
    (hexact : ∀ w, polyMask w = mask w) (hmask : ∀ w, |mask w| ≤ 1)
    (p : ℕ) (hp : Nat.Prime p) (e : ℕ) (he : 1 ≤ e)
    (scores : W → Forms → ℤ) (rho : Forms → ℤ)
    (hguard : 2 * (∑ w, |g w|) < (p : ℤ) ^ e) :
    centeredResidue ((p : ℤ) ^ e) (residuePolynomial g polyMask p e scores rho) =
      residueCount g mask p scores rho := by
  have hq : 0 < (p : ℤ) ^ e := by
    have hp' : (0 : ℤ) < p := by exact_mod_cast hp.pos
    exact pow_pos hp' _
  have hbound := residueCount_abs_le g mask hmask p scores rho
  have hlo := neg_abs_le (residueCount g mask p scores rho)
  have hup := le_abs_self (residueCount g mask p scores rho)
  apply centeredResidue_eq _ _ _ hq
    (residuePolynomial_modEq_count g polyMask mask hexact p hp e he scores rho)
  · omega
  · omega

/-- Paper `lem:residue`, paper/paper.tex: the recovered count is the UNIQUE
integer in the full centered interval, not merely a matching residue. -/
theorem centered_representative_unique (q value answer : ℤ) (hq : 0 < q)
    (hmod : value ≡ answer [ZMOD q])
    (hlow : -q < 2 * answer) (hup : 2 * answer ≤ q) :
    ∃! result : ℤ, -q < 2 * result ∧ 2 * result ≤ q ∧ value ≡ result [ZMOD q] := by
  refine ⟨answer, ⟨hlow, hup, hmod⟩, ?_⟩
  intro result hresult
  have ha := centeredResidue_eq q value answer hq hmod hlow hup
  have hr := centeredResidue_eq q value result hq hresult.2.2 hresult.1 hresult.2.1
  exact hr.symm.trans ha

end NearQuarticWires.Walks
