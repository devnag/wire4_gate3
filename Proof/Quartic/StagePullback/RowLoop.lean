import Proof.Quartic.StagePullback.RowPrefix
import Proof.Quartic.StagePullback.CoordinateProgram

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePullback.NativeRows

open NearCubicWires
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicGates.Close.Cells
open NearCubicGates.Close.WordPrograms

def loopScratch : List (Fin VV) := MarkerCalls.originalCoordinate :: rowScratch

/-- `prop:time`, paper/paper.tex: linear additional
binary width covers the mass of all original signed source fields. -/
theorem rowAccumulatorWidth (C : Ctx) (n Lin : ℕ) (hwidth : Lin + n + 6 ≤ C.Wd) :
    (n + 1) * 2 ^ Lin < 2 ^ C.Wd := by
  have hn := Nat.lt_two_pow_self (n := n + 1)
  have hp : (n + 1) * 2 ^ Lin < 2 ^ (n + 1 + Lin) := by
    rw [pow_add]
    exact Nat.mul_lt_mul_of_pos_right hn (Nat.two_pow_pos _)
  exact hp.trans_le (Nat.pow_le_pow_right (by decide) (by omega))

/-- `imp:pullback`, paper/paper.tex: the physical
row-loop invariant records exact native prefixes and exact affine target
and mass prefixes after k original coordinates. -/
structure RowState (C : Ctx) (a : DS VV MM) (q : PointRequest)
    (e : ExactThresholdGate q.parameters.n) (transpose : Bool) (Lin : ℕ)
    (after : List Bool) (k : ℕ) (b : DS VV MM) : Prop where
  frame : Fr a b loopScratch
  cursor : b.ip = a.ip + k * Lin
  source : C.inp.drop b.ip = ((List.ofFn e.weight).drop k).flatMap
    (fun z => binary Lin (SInt.encS z)) ++ after
  output : b.out = a.out
  left : b.ram leftStore = rowNumbers q e transpose true k
  right : b.ram rightStore = rowNumbers q e transpose false k
  leftCursor : b.rc leftStore = (rowNumbers q e transpose true k).length
  rightCursor : b.rc rightStore = (rowNumbers q e transpose false k).length
  difference : (b.env SignedCoefficients.positive : ℤ) - b.env SignedCoefficients.negative =
    -targetPrefix q e k
  mass : b.env SignedCoefficients.positive + b.env SignedCoefficients.negative = massPrefix q e k

/-- `imp:pullback`, paper/paper.tex: the literal loop
reads every original coefficient exactly once in original coordinate order. -/
def rowProgram : St VV MM := forS MarkerCalls.originalCoordinate 20 coordinateRowProgram

/-- `imp:pullback` and `prop:time`, paper/paper.tex: the complete original-coordinate loop physically builds
both signed native coefficient stores, with exact target and mass, using
actual canonical flips and side placement at every coordinate. -/
theorem rowProgram_run (C : Ctx) (a : DS VV MM) (q : PointRequest)
    (e : ExactThresholdGate q.parameters.n) (transpose : Bool) (Lin : ℕ) (after : List Bool)
    (hi : Flips.Inputs a q (firstCoordinate q)) (hwidth : Lin + q.parameters.n + 6 ≤ C.Wd)
    (hn : a.env 20 = q.parameters.n) (hfield : a.env fieldWidth = Lin)
    (hfit : ∀ i, SInt.encS (e.weight i) < 2 ^ Lin)
    (hin : C.inp.drop a.ip = (List.ofFn e.weight).flatMap
      (fun z => binary Lin (SInt.encS z)) ++ after)
    (hleft : a.env Sides.leftEnd = q.parameters.r / 2 * q.parameters.b)
    (hblock : a.env Sides.blockedEnd = q.parameters.r * q.parameters.b)
    (hfree : a.env Sides.freeLeftEnd =
      q.parameters.r * q.parameters.b + (q.parameters.n - q.parameters.r * q.parameters.b + 1) / 2)
    (ht : a.env transposeFlag = transpose.toNat)
    (hl0 : a.ram leftStore = []) (hr0 : a.ram rightStore = [])
    (hlc0 : a.rc leftStore = 0) (hrc0 : a.rc rightStore = 0)
    (hp0 : a.env SignedCoefficients.positive = 0) (hn0 : a.env SignedCoefficients.negative = 0) :
    Hs C rowProgram a
      (q.parameters.n * (10 * Lin + 21 * q.parameters.n + 204) + 4) (fun b =>
        RowState C a q e transpose Lin after q.parameters.n b ∧
        b.env MarkerCalls.originalCoordinate = q.parameters.n ∧ b.env 20 = q.parameters.n) := by
  let I := RowState C a q e transpose Lin after
  have h0 : I 0 a := by
    refine ⟨Fr.refl _ _, by simp, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa using hin
    · simpa [rowNumbers] using hl0
    · simpa [rowNumbers] using hr0
    · simp [rowNumbers, hlc0]
    · simp [rowNumbers, hrc0]
    · simp [hp0, hn0, targetPrefix]
    · simp [hp0, hn0, massPrefix]
  have hI : ∀ k b v, I k b → I k (b.set MarkerCalls.originalCoordinate v) := by
    intro k b v h
    refine ⟨h.frame.trans (Fr.set b _ (by simp [loopScratch])), h.cursor, h.source,
      h.output, h.left, h.right, h.leftCursor, h.rightCursor, ?_, ?_⟩
    · rw [DS.set_env_ne _ _ (by decide : SignedCoefficients.positive ≠ MarkerCalls.originalCoordinate),
        DS.set_env_ne _ _ (by decide : SignedCoefficients.negative ≠ MarkerCalls.originalCoordinate)]
      exact h.difference
    · rw [DS.set_env_ne _ _ (by decide : SignedCoefficients.positive ≠ MarkerCalls.originalCoordinate),
        DS.set_env_ne _ _ (by decide : SignedCoefficients.negative ≠ MarkerCalls.originalCoordinate)]
      exact h.mass
  have hnfit := (Flips.markerWidth C q.parameters (by omega)).2.2.2
  unfold rowProgram
  refine forS_spec' MarkerCalls.originalCoordinate 20 (by decide) coordinateRowProgram a
    q.parameters.n hnfit I (10 * Lin + 21 * q.parameters.n + 200) hI h0 hn ?_
  intro k hk b hb hki hcn
  let x : Fin q.parameters.n := ⟨k, hk⟩
  have hbc : Cst b := hi.constants.of_fr hb.frame (by decide)
  have hbi : Flips.Inputs b q x := ⟨hbc,
    (hb.frame _ (by decide)).trans hi.blocks,
    (hb.frame _ (by decide)).trans hi.translation,
    (hb.frame _ (by decide)).trans hi.left,
    (hb.frame _ (by decide)).trans hi.right,
    (hb.frame _ (by decide)).trans hi.useLeft,
    (hb.frame _ (by decide)).trans hi.useRight,
    (hb.frame _ (by decide)).trans hi.half,
    hki, (hb.frame _ (by decide)).trans hi.blockWidth,
    (hb.frame _ (by decide)).trans hi.radix⟩
  have hdrop : (List.ofFn e.weight).drop k = e.weight x :: (List.ofFn e.weight).drop (k + 1) := by
    have hh := List.drop_eq_getElem_cons (l := List.ofFn e.weight) (by simpa using hk)
    rw [List.getElem_ofFn] at hh
    exact hh
  let tail := ((List.ofFn e.weight).drop (k + 1)).flatMap
    (fun z => binary Lin (SInt.encS z)) ++ after
  have hinput : C.inp.drop b.ip = binary Lin (SInt.encS (e.weight x)) ++ tail := by
    rw [hb.source, hdrop, List.flatMap_cons, List.append_assoc]
  have habs : (e.weight x).natAbs ≤ 2 ^ Lin := by
    have hh := hfit x
    unfold SInt.encS at hh
    split_ifs at hh <;> omega
  have htotal : b.env SignedCoefficients.positive + b.env SignedCoefficients.negative +
      (e.weight x).natAbs < 2 ^ C.Wd := by
    calc
      _ = massPrefix q e k + (e.weight x).natAbs := by rw [hb.mass]
      _ ≤ k * 2 ^ Lin + 2 ^ Lin := Nat.add_le_add (massPrefix_le q e Lin k hk.le hfit) habs
      _ = (k + 1) * 2 ^ Lin := by ring
      _ ≤ (q.parameters.n + 1) * 2 ^ Lin := Nat.mul_le_mul_right _ (by omega)
      _ < 2 ^ C.Wd := rowAccumulatorWidth C q.parameters.n Lin hwidth
  have hrun := coordinateRowProgram_run C b q x (e.weight x) transpose Lin tail hbi (by omega)
    ((hb.frame _ (by decide)).trans hfield) (by omega) (hfit x) hinput
    ((hb.frame _ (by decide)).trans hleft) ((hb.frame _ (by decide)).trans hblock)
    ((hb.frame _ (by decide)).trans hfree) ((hb.frame _ (by decide)).trans ht)
    (by omega) (by omega) (by rw [hb.leftCursor, hb.left]) (by rw [hb.rightCursor, hb.right])
  refine Hs.mono hrun (by
    have hh : x.val / q.parameters.b ≤ q.parameters.n :=
      (Nat.div_le_self _ _).trans hk.le
    omega) ?_
  rintro d ⟨_, hddiff, hdmass, hdip, hdout, hdram, hdrc, _, hdfr⟩
  have hsideCode : coordinateSide q transpose k = xor (q.parameters.centerSide x) transpose := by
    rw [coordinateSide, dif_pos hk]
  have hflipCode : coordinateFlip q k = q.flip x := by rw [coordinateFlip, dif_pos hk]
  have hweightCode : originalWeight q e k = e.weight x := by rw [originalWeight, dif_pos hk]
  have hBL : b.ram (0 : Fin MM) = rowNumbers q e transpose true k := hb.left
  have hBR : b.ram (1 : Fin MM) = rowNumbers q e transpose false k := hb.right
  have hBC0 : b.rc (0 : Fin MM) = (rowNumbers q e transpose true k).length := hb.leftCursor
  have hBC1 : b.rc (1 : Fin MM) = (rowNumbers q e transpose false k).length := hb.rightCursor
  have hstate : I (k + 1) d := by
    refine ⟨hb.frame.trans (hdfr.weaken (by
      intro y hy
      exact List.mem_cons_of_mem MarkerCalls.originalCoordinate hy)), ?_, ?_,
      hdout.trans hb.output, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hdip, hb.cursor]
      ring
    · rw [hdip, ← List.drop_drop, hinput]
      simp [NearCubicWires.RepairOrdinary.SignedSortKey.binary_length, tail]
    · rw [hdram, rowNumbers_succ, hsideCode, hflipCode, hweightCode]
      cases hside : xor (q.parameters.centerSide x) transpose <;>
        simp [hside, putAt, hBL, hBR, hBC0, hBC1, leftStore, rightStore]
    · rw [hdram, rowNumbers_succ, hsideCode, hflipCode, hweightCode]
      cases hside : xor (q.parameters.centerSide x) transpose <;>
        simp [hside, putAt, hBL, hBR, hBC0, hBC1, leftStore, rightStore]
    · rw [hdrc, rowNumbers_succ, hsideCode, hflipCode, hweightCode]
      cases hside : xor (q.parameters.centerSide x) transpose <;>
        simp [hside, hBC0, hBC1, leftStore, rightStore]
    · rw [hdrc, rowNumbers_succ, hsideCode, hflipCode, hweightCode]
      cases hside : xor (q.parameters.centerSide x) transpose <;>
        simp [hside, hBC0, hBC1, leftStore, rightStore]
    · rw [hddiff, hb.difference, targetPrefix_succ]
      rw [hflipCode, hweightCode]
      ring
    · rw [hdmass, hb.mass, massPrefix_succ]
      rw [hflipCode, hweightCode]
  exact ⟨hstate, (hdfr _ (by decide)).trans hki, (hdfr _ (by decide)).trans hcn⟩

end NearQuarticWires.StagePullback.NativeRows
