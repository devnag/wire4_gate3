import Proof.Quartic.Sampler.CellFourier
import Proof.Quartic.Sampler.Parity

set_option autoImplicit false

namespace NearQuarticWires.Sampler

open Finset
open NearCubicWires NearCubicWires.WireExponent3_5.Shared

/-- `lem:fourier`, paper/paper.tex: the parity character of a bit. -/
def bitSign (b : Bool) : ℂ := if b then -1 else 1

/-- `lem:fourier`, paper/paper.tex: XOR multiplies the sign characters. -/
theorem bitSign_xor (a b : Bool) : bitSign (xor a b) = bitSign a * bitSign b := by
  cases a <;> cases b <;> norm_num [bitSign]

/-- `lem:fourier`, paper/paper.tex: a list parity is the product
of its ORIGINAL input-bit characters (arbitrary initial accumulator retained). -/
theorem bitSign_foldl {α : Type} (l : List α) (x : α → Bool) (b : Bool) :
    bitSign (l.foldl (fun p i => xor p (x i)) b) =
      bitSign b * (l.map fun i => bitSign (x i)).prod := by
  induction l generalizing b with
  | nil => simp
  | cons i l ih =>
    simp only [List.foldl_cons, List.map_cons, List.prod_cons, ih, bitSign_xor]
    ring

/-- `lem:fourier`, paper/paper.tex: the actual source input parity sign. -/
noncomputable def paritySign {n : ℕ} (A : Finset (Fin n)) (x : BitInput n) : ℂ :=
  bitSign (NearCubicWires.SourceInterfaces.parityOn A x)

/-- `lem:fourier`, paper/paper.tex: parity linearity on ORIGINAL
input XOR; it does not depend on star partition geometry or source randomness. -/
theorem paritySign_xorInput {n : ℕ} (A : Finset (Fin n)) (x y : BitInput n) :
    paritySign A (xorInput x y) = paritySign A x * paritySign A y := by
  unfold paritySign NearCubicWires.SourceInterfaces.parityOn
  rw [bitSign_foldl, bitSign_foldl, bitSign_foldl]
  simp only [bitSign, Bool.false_eq_true, if_false, one_mul]
  have hpoint : ∀ i, bitSign (xorInput x y i) = bitSign (x i) * bitSign (y i) :=
    fun i => bitSign_xor _ _
  change (A.toList.map fun i => bitSign (xorInput x y i)).prod =
    (A.toList.map fun i => bitSign (x i)).prod * (A.toList.map fun i => bitSign (y i)).prod
  simp_rw [hpoint]
  exact List.prod_map_mul

/-- `lem:fourier`, paper/paper.tex: parity signs are unimodular selectors. -/
theorem norm_paritySign {n : ℕ} (A : Finset (Fin n)) (x : BitInput n) :
    ‖paritySign A x‖ = 1 := by
  unfold paritySign bitSign
  split_ifs <;> simp

/-- `lem:fourier`, paper/paper.tex: actual product-star parity
factors as the column sign, a left selector, and a right selector. -/
theorem paritySign_point (P : StarParams) (A : Finset (Fin P.n))
    (c : BitInput P.n) (u v : P.Errors) :
    paritySign A (P.point c u v) =
      (paritySign A c * paritySign A (P.errorVector P.leftBlock u)) *
        paritySign A (P.errorVector P.rightBlock v) := by
  unfold StarParams.point
  rw [paritySign_xorInput, paritySign_xorInput]

/-- `lem:fourier`, paper/paper.tex: the ACTUAL sign lookup Γ_g,
extended by zero outside the bounded score box. -/
noncomputable def signLookupExtension (m G₁ G₂ : ℕ) (g : ℕ × ℕ → Bool)
    (t : Frequency m G₁ G₂) : ℂ :=
  lookupExtension m G₁ G₂ (fun _ => true) t - 2 * lookupExtension m G₁ G₂ g t

/-- `lem:fourier`, paper/paper.tex: Γ_g is bounded by one everywhere. -/
theorem norm_signLookupExtension_le (m G₁ G₂ : ℕ) (g : ℕ × ℕ → Bool)
    (t : Frequency m G₁ G₂) : ‖signLookupExtension m G₁ G₂ g t‖ ≤ 1 := by
  unfold signLookupExtension lookupExtension
  split_ifs with h
  · cases g (t.1.val, t.2.val) <;> norm_num [boolBit]
  · simp

/-- `lem:fourier`, paper/paper.tex: exact sign lookup on actual scores. -/
theorem signLookupExtension_cast {m G₁ G₂ : ℕ} (hm : 1 ≤ m)
    (g : ℕ × ℕ → Bool) (s₁ s₂ : ℤ)
    (hs₁ : 0 ≤ s₁ ∧ s₁ ≤ G₁) (hs₂ : 0 ≤ s₂ ∧ s₂ ≤ G₂) :
    signLookupExtension m G₁ G₂ g
      ((s₁ : ZMod (omega m G₁)), (s₂ : ZMod (omega m G₂))) =
      bitSign (g (s₁.toNat, s₂.toNat)) := by
  unfold signLookupExtension
  rw [lookupExtension_cast hm _ _ _ hs₁ hs₂,
    lookupExtension_cast hm _ _ _ hs₁ hs₂]
  cases g (s₁.toNat, s₂.toNat) <;> norm_num [boolBit, bitSign]

/-- `lem:fourier`, paper/paper.tex: the ACTUAL Boolean parity
call on product-star cells, with the original input support and actual occurrence
scores. Setting gates₂=[] gives the counter's single-circuit parity call. -/
theorem cell_parity_call_formula (P : StarParams) (m : ℕ) (hm : 1 ≤ m)
    (gates₁ gates₂ : List (NormalizedThresholdGate P.n))
    (g : ℕ × ℕ → Bool) (A : Finset (Fin P.n)) (c : BitInput P.n)
    (u v : P.Errors) :
    boolBit (xor (g ((NearQuarticWires.Cells.score P gates₁ c u v).toNat,
      (NearQuarticWires.Cells.score P gates₂ c u v).toNat))
      (NearCubicWires.SourceInterfaces.parityOn A (P.point c u v))) =
    (1 / 2 : ℂ) - (1 / 2 : ℂ) *
      (paritySign A c * paritySign A (P.errorVector P.leftBlock u)) *
      paritySign A (P.errorVector P.rightBlock v) *
      signLookupExtension m gates₁.length gates₂.length g
        (((NearQuarticWires.Cells.score P gates₁ c u v : ℤ) :
            ZMod (omega m gates₁.length)),
         ((NearQuarticWires.Cells.score P gates₂ c u v : ℤ) :
            ZMod (omega m gates₂.length))) := by
  rw [signLookupExtension_cast hm g _ _
    (NearQuarticWires.Cells.score_bounds P gates₁ c u v)
    (NearQuarticWires.Cells.score_bounds P gates₂ c u v)]
  have hx := xor_bit_identity
    (g ((NearQuarticWires.Cells.score P gates₁ c u v).toNat,
      (NearQuarticWires.Cells.score P gates₂ c u v).toNat))
    (NearCubicWires.SourceInterfaces.parityOn A (P.point c u v))
  change boolBit _ = _ at hx
  rw [hx]
  change (1 / 2 : ℂ) - (1 / 2 : ℂ) * bitSign _ * paritySign A (P.point c u v) = _
  rw [paritySign_point]
  ring

end NearQuarticWires.Sampler
