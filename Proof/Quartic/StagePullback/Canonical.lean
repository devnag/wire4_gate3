import Proof.Wire_3_5.PrimTC4GeoV
import Proof.Wire_3_5.FinalPassSampleRef

set_option autoImplicit false

namespace NearQuarticWires.StagePullback

open NearCubicWires NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.Shared

/-- `imp:partition` and `imp:pullback`, paper/paper.tex: a low-first block digit of an encoded translation or error. -/
def blockDigit (s code block : ℕ) : ℕ := code / (2 ^ s) ^ block % 2 ^ s

/-- `imp:partition`, paper/paper.tex: the canonical
low-first code of all block syndromes of a star translation. -/
def translationNumber (P : StarParams) (σ : P.Translation) : ℕ :=
  (((Equiv.piCongrRight fun _ => finFunctionFinEquiv).trans finFunctionFinEquiv) σ).val

/-- `imp:partition`, paper/paper.tex: the literal
syndrome of a block is the corresponding low-first radix digit. -/
theorem translationNumber_digit (P : StarParams) (σ : P.Translation) (j : Fin P.r) :
    (finFunctionFinEquiv (σ j)).val = blockDigit P.s (translationNumber P σ) j.val := by
  have h := congrArg (fun f : Fin P.r → Fin (2 ^ P.s) => (f j).val)
    (finFunctionFinEquiv.symm_apply_apply (fun i : Fin P.r => finFunctionFinEquiv (σ i)))
  simp only [finFunctionFinEquiv_symm_apply_val] at h
  exact h.symm

/-- `imp:pullback`, paper/paper.tex: a coset offset
has its sole block bit at the nonzero syndrome index. -/
theorem offBlock_code (P : StarParams) (σ : P.Translation) (j : Fin P.r) (i : Fin P.b) :
    PrimT.C4Geo.offBlock P σ j i =
      decide ((finFunctionFinEquiv (σ j)).val = i.val + 1) := by
  unfold PrimT.C4Geo.offBlock StarParams.errBits StarParams.errorOf
  have hz : P.syndrome (fun _ => false) = 0 := by simp [StarParams.syndrome]
  simp only [hz, zero_add]
  by_cases hσ : σ j = 0
  · simp [hσ]
  · rw [if_neg hσ]
    have hp : 0 < (finFunctionFinEquiv (σ j)).val := by
      by_contra h
      apply hσ
      apply finFunctionFinEquiv.injective
      apply Fin.ext
      rw [finFunctionFinEquiv_zero]
      omega
    apply decide_eq_decide.mpr
    simp only [Option.some.injEq, Fin.ext_iff]
    omega

/-- `imp:pullback`, paper/paper.tex: the offset at
an original coordinate is obtained directly from its block digit. -/
def offsetBit (r b s code x : ℕ) : Bool :=
  decide (x < r * b ∧ blockDigit s code (x / b) = x % b + 1)

/-- `imp:pullback`, paper/paper.tex: the scalar
offset computation is the actual star coset offset in original order. -/
theorem offsetBit_eq (P : StarParams) (σ : P.Translation) (x : Fin P.n) :
    offsetBit P.r P.b P.s (translationNumber P σ) x.val = PrimT.C4Geo.offset P σ x := by
  by_cases hx : x.val < P.r * P.b
  · let j : Fin P.r := ⟨x.val / P.b, (Nat.div_lt_iff_lt_mul P.b_pos).mpr hx⟩
    let i : Fin P.b := ⟨x.val % P.b, Nat.mod_lt _ P.b_pos⟩
    have he : P.blockCoord j i = x := by
      apply Fin.ext
      exact Nat.div_add_mod' _ _
    calc
      offsetBit P.r P.b P.s (translationNumber P σ) x.val =
          decide (blockDigit P.s (translationNumber P σ) j.val = i.val + 1) := by
        simp only [offsetBit, hx, true_and, j, i]
      _ = PrimT.C4Geo.offBlock P σ j i := by rw [offBlock_code, translationNumber_digit]
      _ = PrimT.C4Geo.offset P σ x := by rw [← he, PrimT.C4Geo.offset_block]
  · rw [PrimT.C4Geo.offset_free P σ x (by omega)]
    simp [offsetBit, hx]

/-- `imp:partition` and `imp:pullback`, paper/paper.tex: the error coordinate is the marker of its side's encoded
block choice, with zero on all other coordinates. -/
def errorBit (b half s : ℕ) (right : Bool) (code x : ℕ) : Bool :=
  decide (FinalPass.Sample.decAt b half right (blockDigit s code) x)

/-- `imp:pullback`, paper/paper.tex: a left error
marker is the offset marker restricted to the left half's blocks. -/
theorem errorBit_left (b half s code x : ℕ) :
    errorBit b half s false code x = offsetBit half b s code x := rfl

/-- `imp:pullback`, paper/paper.tex: the right error
uses the same marker computation after shifting the coordinate origin. -/
theorem errorBit_right (b half s code x : ℕ) :
    errorBit b half s true code x =
      (decide (half * b ≤ x) && offsetBit half b s code (x - half * b)) := by
  unfold errorBit offsetBit FinalPass.Sample.decAt
  simp only [ite_true]
  by_cases hx : half * b ≤ x
  · simp only [hx, decide_true, Bool.true_and, true_and]
    apply decide_eq_decide.mpr
    have he : x < half * b + half * b ↔ x - half * b < half * b := by omega
    rw [he]
  · simp only [hx, decide_false, Bool.false_and, false_and]

/-- `imp:pullback`, paper/paper.tex: the scalar error
coordinate is exactly the literal mixed-radix star error vector. -/
theorem errorBit_eq (P : StarParams) (right : Bool)
    (code : Fin ((P.b + 1) ^ (P.r / 2))) (x : Fin P.n) :
    errorBit P.b (P.r / 2) P.s right code.val x.val =
      P.errorVector (if right then P.rightBlock else P.leftBlock)
        ((FinalPass.errorsEquiv P).symm code) x := by
  have h := congrArg (fun w : List Bool => w[x.val]?)
    (FinalPass.Sample.errorVector_decode P right code)
  rw [FinalPass.Sample.digitsOf_binary] at h
  rw [FinalPass.Sample.decWord_get P.b (P.r / 2) (P.n - P.r * P.b) P.b_pos right
    (fun j => code.val / 2 ^ (P.s * j) % 2 ^ P.s) x.val] at h
  have hlen : P.r / 2 * P.b + P.r / 2 * P.b + (P.n - P.r * P.b) = P.n := by
    have hhalf := P.r_half_add
    have hrb := P.r_mul_b_le
    rw [← Nat.add_mul, hhalf]
    omega
  rw [hlen, if_pos x.isLt] at h
  simp only [List.getElem?_ofFn, dif_pos x.isLt] at h
  have hd : (fun j => code.val / 2 ^ (P.s * j) % 2 ^ P.s) = blockDigit P.s code.val := by
    funext j
    simp only [blockDigit, pow_mul]
  rw [hd] at h
  exact (Option.some.inj h).symm

/-- `imp:pullback` and `lem:print`, paper/paper.tex: the complete affine flip at an original coordinate. -/
def flipBit (r b s translation left right x : ℕ) (useLeft useRight : Bool) : Bool :=
  xor (xor (offsetBit r b s translation x)
    (useLeft && errorBit b (r / 2) s false left x))
    (useRight && errorBit b (r / 2) s true right x)

/-- `imp:pullback`, paper/paper.tex: the decoded affine
flip uses the actual translation and the actual two star errors. -/
theorem flipBit_eq (P : StarParams) (σ : P.Translation)
    (left right : Fin ((P.b + 1) ^ (P.r / 2))) (x : Fin P.n)
    (useLeft useRight : Bool) :
    flipBit P.r P.b P.s (translationNumber P σ) left.val right.val x.val useLeft useRight =
      xor (xor (PrimT.C4Geo.offset P σ x)
        (useLeft && P.errorVector P.leftBlock ((FinalPass.errorsEquiv P).symm left) x))
        (useRight && P.errorVector P.rightBlock ((FinalPass.errorsEquiv P).symm right) x) := by
  rw [flipBit, offsetBit_eq, errorBit_eq, errorBit_eq]
  rfl

end NearQuarticWires.StagePullback
