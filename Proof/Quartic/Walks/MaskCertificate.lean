import Proof.Quartic.Walks.Moments
import Proof.Quartic.Mask.Polynomial
import Proof.Quartic.Cycle.Basic

set_option autoImplicit false

namespace NearQuarticWires.Walks

open scoped BigOperators

/-- Paper `eq:testX`, paper/paper.tex: the points retained by the structural
mask, the ACTUAL index set for the first certificate. -/
abbrev StructuralPoint {N : ℕ} (structural : Sampler.Cell N → Bool) :=
  {x : Sampler.Cell N // structural x = true}

/-- Paper `sec:walks`, paper/paper.tex: `W_s`, the concrete closed walks
whose every edge survives the structural mask. -/
abbrev StructuralWalk {N m : ℕ} (hm : 0 < m)
    (structural : Sampler.Cell N → Bool) :=
  {w : Cycle.Walk N m // ∀ l, structural (Cycle.edge hm w l) = true}

/-- Paper `lem:cycle`, paper/paper.tex: the exact INTEGER product mask on
the actual cycle edges. -/
def walkMaskInt {N m : ℕ} (hm : 0 < m) (structural : Sampler.Cell N → Bool)
    (tau : ℕ) (X : Sampler.Cell N → ℕ) (w : Cycle.Walk N m) : ℤ :=
  ∏ l, Mask.mask (structural (Cycle.edge hm w l)) tau (X (Cycle.edge hm w l))

/-- Paper `eq:testE`/`lem:residue`, paper/paper.tex: the product of
the literal integer Newton polynomials, without a modulus-dependent mask. -/
def walkMaskPoly {N m : ℕ} (hm : 0 < m) (structural : Sampler.Cell N → Bool)
    (tau Xmax : ℕ) (X : Sampler.Cell N → ℕ) (w : Cycle.Walk N m) : ℤ :=
  ∏ l, Mask.maskPolyEval (structural (Cycle.edge hm w l)) tau Xmax (X (Cycle.edge hm w l))

/-- Paper `lem:certify`(a), paper/paper.tex: the FIRST strict moment test
certifies the sampled population at every structurally retained point. -/
theorem testX_bounds_population {N : ℕ} (structural : Sampler.Cell N → Bool)
    (k Xmax : ℕ) (X : Sampler.Cell N → ℕ)
    (htest : momentSum k (fun x : StructuralPoint structural => (X x.val : ℤ)) <
      ((Xmax + 1 : ℕ) : ℤ) ^ (2 * k)) :
    ∀ x, structural x = true → X x ≤ Xmax := by
  intro x hx
  have h := moment_sound k (Xmax + 1)
    (fun x : StructuralPoint structural => (X x.val : ℤ)) htest ⟨x, hx⟩
  have h' : X x < Xmax + 1 := by simpa using h
  omega

/-- Paper `lem:certify`(a), paper/paper.tex: certification, rather than an
honest witness, makes the point mask polynomial exact at EVERY point. -/
theorem testX_maskPoly_exact {N : ℕ} (structural : Sampler.Cell N → Bool)
    (k tau Xmax : ℕ) (X : Sampler.Cell N → ℕ)
    (htest : momentSum k (fun x : StructuralPoint structural => (X x.val : ℤ)) <
      ((Xmax + 1 : ℕ) : ℤ) ^ (2 * k)) (x : Sampler.Cell N) :
    Mask.maskPolyEval (structural x) tau Xmax (X x) = Mask.mask (structural x) tau (X x) := by
  apply Mask.maskPoly_eq_mask
  cases hx : structural x with
  | false => exact Or.inr rfl
  | true => exact Or.inl (testX_bounds_population structural k Xmax X htest x hx)

/-- Paper `lem:certify`(a), paper/paper.tex: the concrete Newton product
agrees with the exact walk mask on ALL walks, including structural zeros. -/
theorem testX_walkMaskPoly_exact {N m : ℕ} (hm : 0 < m)
    (structural : Sampler.Cell N → Bool) (k tau Xmax : ℕ) (X : Sampler.Cell N → ℕ)
    (htest : momentSum k (fun x : StructuralPoint structural => (X x.val : ℤ)) <
      ((Xmax + 1 : ℕ) : ℤ) ^ (2 * k)) (w : Cycle.Walk N m) :
    walkMaskPoly hm structural tau Xmax X w = walkMaskInt hm structural tau X w := by
  apply Finset.prod_congr rfl
  intro l _
  exact testX_maskPoly_exact structural k tau Xmax X htest (Cycle.edge hm w l)

/-- Paper `def:mask`/`lem:certify`, paper/paper.tex: every exact walk
mask is an integer Boolean bit; repeated edges do not alter this fact. -/
theorem walkMaskInt_zero_or_one {N m : ℕ} (hm : 0 < m)
    (structural : Sampler.Cell N → Bool) (tau : ℕ) (X : Sampler.Cell N → ℕ)
    (w : Cycle.Walk N m) :
    walkMaskInt hm structural tau X w = 0 ∨ walkMaskInt hm structural tau X w = 1 := by
  classical
  by_cases hz : ∃ l, Mask.mask (structural (Cycle.edge hm w l)) tau (X (Cycle.edge hm w l)) = 0
  · left
    obtain ⟨l, hl⟩ := hz
    exact Finset.prod_eq_zero (Finset.mem_univ l) hl
  · right
    apply Finset.prod_eq_one
    intro l _
    exact (Mask.mask_zero_or_one _ _ _).resolve_left (fun h => hz ⟨l, h⟩)

/-- Paper `lem:certify`(b), paper/paper.tex: a walk of exact mask one is
in the ACTUAL structural walk set used in the printed moment tests. -/
theorem retained_walk_structural {N m : ℕ} (hm : 0 < m)
    (structural : Sampler.Cell N → Bool) (tau : ℕ) (X : Sampler.Cell N → ℕ)
    (w : Cycle.Walk N m) (hw : walkMaskInt hm structural tau X w = 1) :
    ∀ l, structural (Cycle.edge hm w l) = true := by
  classical
  intro l
  by_contra hn
  have hz : Mask.mask (structural (Cycle.edge hm w l)) tau (X (Cycle.edge hm w l)) = 0 := by
    simp [Mask.mask, hn]
  have hp : walkMaskInt hm structural tau X w = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ l) hz
  omega

/-- Paper `lem:residue`, paper/paper.tex: the exact walk mask has absolute
value at most one, as required by signed residue mass bounds. -/
theorem walkMaskInt_abs_le_one {N m : ℕ} (hm : 0 < m)
    (structural : Sampler.Cell N → Bool) (tau : ℕ) (X : Sampler.Cell N → ℕ)
    (w : Cycle.Walk N m) : |walkMaskInt hm structural tau X w| ≤ 1 := by
  rcases walkMaskInt_zero_or_one hm structural tau X w with h | h <;> simp [h]

end NearQuarticWires.Walks
