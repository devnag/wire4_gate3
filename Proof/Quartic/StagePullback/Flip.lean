import Proof.Quartic.StagePullback.MarkerCall
import Proof.Quartic.StagePullback.ScalarPoint

set_option autoImplicit false

namespace NearQuarticWires.StagePullback.Flips

open NearCubicWires NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.Shared
open NearCubicGates.Close.Cells

def accumulator : Fin VV := 94
def halfCount : Fin VV := 33
def leftFlag : Fin VV := 29
def rightFlag : Fin VV := 30

def scratch : List (Fin VV) := accumulator :: MarkerCalls.scratch

/-- `imp:pullback`, paper/paper.tex: every retained
input is an actual scalar code in the compact canonical request. -/
structure Inputs (a : DS VV MM) (q : PointRequest) (x : Fin q.parameters.n) : Prop where
  constants : Cst a
  blocks : a.env 21 = q.parameters.r
  translation : a.env 24 = translationNumber q.parameters q.translation
  left : a.env 27 = q.left.val
  right : a.env 28 = q.right.val
  useLeft : a.env leftFlag = q.useLeft.toNat
  useRight : a.env rightFlag = q.useRight.toNat
  half : a.env halfCount = q.parameters.r / 2
  coordinate : a.env MarkerCalls.originalCoordinate = x.val
  blockWidth : a.env Offsets.blockWidth = q.parameters.b
  radix : a.env Digits.radix = 2 ^ q.parameters.s

/-- `imp:pullback`, paper/paper.tex: all canonical
request fields survive each coordinate computation. -/
theorem Inputs.frame {a b : DS VV MM} {q : PointRequest} {x : Fin q.parameters.n}
    (h : Inputs a q x) (hf : Fr a b scratch) : Inputs b q x := by
  exact ⟨h.constants.of_fr hf (by decide),
    (hf _ (by decide)).trans h.blocks, (hf _ (by decide)).trans h.translation,
    (hf _ (by decide)).trans h.left, (hf _ (by decide)).trans h.right,
    (hf _ (by decide)).trans h.useLeft, (hf _ (by decide)).trans h.useRight,
    (hf _ (by decide)).trans h.half, (hf _ (by decide)).trans h.coordinate,
    (hf _ (by decide)).trans h.blockWidth, (hf _ (by decide)).trans h.radix⟩

/-- `prop:time`, paper/paper.tex: linear binary
workspace covers every original-coordinate marker operation. -/
theorem markerWidth (C : Ctx) (P : StarParams) (hwidth : P.n + 4 ≤ C.Wd) :
    2 * P.b ≤ 2 ^ C.Wd ∧ P.r * P.b < 2 ^ C.Wd ∧
      2 * 2 ^ P.s ≤ 2 ^ C.Wd ∧ P.n < 2 ^ C.Wd := by
  have hb : P.b ≤ P.n :=
    (Nat.le_mul_of_pos_left _ P.r_pos).trans P.r_mul_b_le
  have hn : P.n < 2 ^ C.Wd :=
    (Nat.lt_two_pow_self (n := P.n)).trans_le
      (Nat.pow_le_pow_right (by decide) (by omega))
  have hh : 2 * (P.n + 1) < 2 ^ (P.n + 2) := by
    have hh := Nat.mul_lt_mul_of_pos_left (Nat.lt_two_pow_self (n := P.n + 1))
      (show 0 < 2 by decide)
    simpa only [pow_succ, Nat.mul_comm] using hh
  have hp : 2 ^ (P.n + 2) ≤ 2 ^ C.Wd :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hr : 2 ^ P.s ≤ P.n + 1 := by rw [← P.b_succ]; omega
  exact ⟨(Nat.mul_le_mul_left 2 (by omega : P.b ≤ P.n + 1)).trans (hh.le.trans hp),
    P.r_mul_b_le.trans_lt hn,
    (Nat.mul_le_mul_left 2 hr).trans (hh.le.trans hp), hn⟩

def errorCode (q : PointRequest) (right : Bool) : ℕ := if right then q.right.val else q.left.val
def errorFlag (q : PointRequest) (right : Bool) : Bool := if right then q.useRight else q.useLeft
def codeRegister (right : Bool) : Fin VV := if right then 28 else 27
def flagRegister (right : Bool) : Fin VV := if right then rightFlag else leftFlag

/-- `imp:pullback`, paper/paper.tex: the two physical
error calls use the corresponding retained pattern and the actual half
block count. -/
def errorCall (right : Bool) : St VV MM :=
  if right then MarkerCalls.rightCall halfCount (codeRegister right)
  else MarkerCalls.leftCall halfCount (codeRegister right)

/-- `imp:pullback` and `prop:time`, paper/paper.tex: physical pattern decoding computes the actual selected
side's original-coordinate error bit and retains all metadata. -/
theorem errorCall_run (C : Ctx) (a : DS VV MM) (q : PointRequest)
    (x : Fin q.parameters.n) (hi : Inputs a q x) (right : Bool)
    (hwidth : q.parameters.n + 4 ≤ C.Wd) :
    Hs C (errorCall right) a (7 * (x.val / q.parameters.b) + 32) (fun b =>
      b.env Markers.result =
        (errorBit q.parameters.b (q.parameters.r / 2) q.parameters.s right (errorCode q right) x.val).toNat ∧
      b.sh = a.sh ∧ Fr a b MarkerCalls.scratch) := by
  have hw := markerWidth C q.parameters hwidth
  have hp : q.parameters.r / 2 * q.parameters.b < 2 ^ C.Wd :=
    (Nat.mul_le_mul_right _ (Nat.div_le_self q.parameters.r 2)).trans_lt hw.2.1
  have hcode : a.env (codeRegister right) = errorCode q right := by
    cases right <;> first | exact hi.left | exact hi.right
  have hb := hi.blockWidth
  have hr := hi.radix
  have hh := hi.half
  have hx := hi.coordinate
  have hprod : a.env halfCount * a.env Offsets.blockWidth < 2 ^ C.Wd := by rw [hh, hb]; exact hp
  have hxfit : a.env MarkerCalls.originalCoordinate < 2 ^ C.Wd := by rw [hx]; exact x.isLt.trans hw.2.2.2
  have hright : errorBit q.parameters.b (q.parameters.r / 2) q.parameters.s true
      (errorCode q true) x.val = decide
        (q.parameters.r / 2 * q.parameters.b ≤ x.val ∧
          x.val - q.parameters.r / 2 * q.parameters.b < q.parameters.r / 2 * q.parameters.b ∧
          errorCode q true / (2 ^ q.parameters.s) ^
            ((x.val - q.parameters.r / 2 * q.parameters.b) / q.parameters.b) % 2 ^ q.parameters.s =
            (x.val - q.parameters.r / 2 * q.parameters.b) % q.parameters.b + 1) := by
    rw [errorBit_right]
    by_cases he : q.parameters.r / 2 * q.parameters.b ≤ x.val <;>
      simp [offsetBit, blockDigit, he]
  cases right with
  | false =>
    have hrun := MarkerCalls.leftCall_run C a hi.constants halfCount (codeRegister false)
      (by decide) (by decide) (by rw [hb]; exact q.parameters.b_pos)
      (by rw [hb]; exact hw.1) hprod hxfit
      (by rw [hr]; exact Nat.two_pow_pos _) (by rw [hr]; exact hw.2.2.1)
    refine Hs.mono hrun (by rw [hx, hb]) ?_
    rintro b ⟨hv, hs, hf⟩
    refine ⟨?_, hs, hf⟩
    simpa [hx, hb, hh, hcode, hr, errorBit_left, offsetBit, blockDigit] using hv
  | true =>
    have hrun := MarkerCalls.rightCall_run C a hi.constants halfCount (codeRegister true)
      (by decide) (by decide) (by rw [hb]; exact q.parameters.b_pos)
      (by rw [hb]; exact hw.1) hprod hxfit
      (by rw [hr]; exact Nat.two_pow_pos _) (by rw [hr]; exact hw.2.2.1)
    refine Hs.mono hrun (by rw [hx, hb]) ?_
    rintro b ⟨hv, hs, hf⟩
    refine ⟨?_, hs, hf⟩
    simpa only [hx, hb, hh, hcode, hr, hright] using hv

end NearQuarticWires.StagePullback.Flips
