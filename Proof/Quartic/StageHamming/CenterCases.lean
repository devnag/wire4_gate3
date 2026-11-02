import Proof.Quartic.StageHamming.CenterFree

set_option autoImplicit false

namespace NearQuarticWires.StageHamming

open NearCubicGates.Close.Cells
open NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.Shared

/-- `imp:pullback`, paper/paper.tex: preparing only
the local coordinate preserves every physically computed boundary. -/
theorem CenterReady.local_frame {a b : DS VV MM} {P : StarParams}
    (h : CenterReady a P) (hf : Fr a b [centerLocal]) : CenterReady b P :=
  ⟨(hf _ (by decide)).trans h.half, (hf _ (by decide)).trans h.left,
    (hf _ (by decide)).trans h.blocked, (hf _ (by decide)).trans h.free,
    (hf _ (by decide)).trans h.upper, (hf _ (by decide)).trans h.blockSize,
    (hf _ (by decide)).trans h.parity, (hf _ (by decide)).trans h.dataDimension⟩

/-- `imp:pullback`, paper/paper.tex: a left coded
coordinate uses its original coordinate and the original row code. -/
def centerLeftBlock : St VV MM :=
  .seq (.op (.copy centerLocal 31)) (centerBlock 25)

/-- `imp:pullback` and `prop:time`, paper/paper.tex: the left-block branch computes its exact canonical bit. -/
theorem centerLeftBlock_spec {C : Ctx} (a : DS VV MM) (hc : Cst a)
    (P : StarParams) (row x : ℕ) (hrow : a.env 25 = row) (hx : a.env 31 = x)
    (hready : CenterReady a P) (hxL : x < P.r / 2 * P.b)
    (hwidth : P.n + 4 ≤ C.Wd) :
    Hs C centerLeftBlock a (200 * (P.n + 1) ^ 3 + 18) (fun b =>
      b.env centerOutput = (PrimT.C4Geo.encB P
        (fun m => row.testBit (x / P.b * PrimT.C4Geo.dB P + m)) (x % P.b)).toNat ∧
      b.sh = a.sh ∧ Fr a b centerScratch) := by
  unfold centerLeftBlock
  refine Hx.hs (Hs.then (hs_copy C centerLocal 31 a (by decide))
    (fun b hb n1 hn1 => ?_))
  subst hb
  let a1 := a.set centerLocal (a.env 31)
  have hf : Fr a a1 [centerLocal] := Fr.set _ _ (by simp)
  refine Hs.last (centerBlock_spec a1 (hc.of_fr hf (by decide)) P row x 25 (by decide)
    ((hf _ (by decide)).trans hrow) (by rw [DS.set_env_self, hx])
    (hready.local_frame hf) hxL hwidth) ?_
  rintro b ⟨hv, hsh, hfr⟩ n2 hn2
  exact ⟨⟨hv, hsh, (hf.weaken (by decide)).trans hfr⟩, by omega⟩

/-- `imp:pullback`, paper/paper.tex: a right coded
coordinate is translated by the left coded width before encoding. -/
def centerRightBlock : St VV MM :=
  .seq (.op (.copy centerLocal 31))
    (.seq (.op (.sub centerLocal centerLeft)) (centerBlock 26))

/-- `imp:pullback` and `prop:time`, paper/paper.tex: the right-block branch retains the actual original
column code and computes its exact canonical local block bit. -/
theorem centerRightBlock_spec {C : Ctx} (a : DS VV MM) (hc : Cst a)
    (P : StarParams) (column x : ℕ) (hcolumn : a.env 26 = column) (hx : a.env 31 = x)
    (hready : CenterReady a P) (hxL : P.r / 2 * P.b ≤ x) (hxB : x < P.r * P.b)
    (hwidth : P.n + 4 ≤ C.Wd) :
    Hs C centerRightBlock a (200 * (P.n + 1) ^ 3 + 20) (fun b =>
      b.env centerOutput = (PrimT.C4Geo.encB P
        (fun m => column.testBit ((x - P.r / 2 * P.b) / P.b * PrimT.C4Geo.dB P + m))
        ((x - P.r / 2 * P.b) % P.b)).toNat ∧
      b.sh = a.sh ∧ Fr a b centerScratch) := by
  unfold centerRightBlock
  refine Hx.hs (Hs.then (hs_copy C centerLocal 31 a (by decide))
    (fun b hb n1 hn1 => ?_))
  subst hb
  let a1 := a.set centerLocal (a.env 31)
  refine Hs.then (hs_sub C centerLocal centerLeft a1 (by decide)
    (by simpa (config := { decide := true }) [a1, DS.set, hx, hready.left] using hxL))
    (fun b hb n2 hn2 => ?_)
  subst hb
  let a2 := a1.set centerLocal (a1.env centerLocal - a1.env centerLeft)
  have hf : Fr a a2 [centerLocal] :=
    (Fr.set a _ (by simp)).trans (Fr.set a1 _ (by simp))
  have hlocal : a2.env centerLocal = x - P.r / 2 * P.b := by
    vsimp [a2, a1, hx, hready.left]
  have hz : x - P.r / 2 * P.b < P.r / 2 * P.b := by
    have h := PrimT.C4Geo.rb_eq P
    omega
  refine Hs.last (centerBlock_spec a2 (hc.of_fr hf (by decide)) P column
    (x - P.r / 2 * P.b) 26 (by decide) ((hf _ (by decide)).trans hcolumn)
    hlocal (hready.local_frame hf) hz hwidth) ?_
  rintro b ⟨hv, hsh, hfr⟩ n3 hn3
  exact ⟨⟨hv, hsh, (hf.weaken (by decide)).trans hfr⟩, by omega⟩

/-- `imp:pullback`, paper/paper.tex: the left free
tail subtracts precisely the original coded-coordinate boundary. -/
def centerLeftFree : St VV MM :=
  .seq (.op (.copy centerLocal 31))
    (.seq (.op (.sub centerLocal centerBlocked)) (centerFreeBit 25))

/-- `imp:pullback` and `prop:time`, paper/paper.tex: the left free-tail branch returns its literal row bit. -/
theorem centerLeftFree_spec {C : Ctx} (a : DS VV MM) (hc : Cst a)
    (P : StarParams) (row x : ℕ) (hrow : a.env 25 = row) (hx : a.env 31 = x)
    (hready : CenterReady a P) (hxB : P.r * P.b ≤ x) (hxN : x < P.n)
    (hwidth : P.n + 4 ≤ C.Wd) :
    Hs C centerLeftFree a (10 * P.n + 36) (fun b =>
      b.env centerOutput =
        (row.testBit (P.r / 2 * PrimT.C4Geo.dB P + (x - P.r * P.b))).toNat ∧
      b.sh = a.sh ∧ Fr a b centerScratch) := by
  unfold centerLeftFree
  refine Hx.hs (Hs.then (hs_copy C centerLocal 31 a (by decide))
    (fun b hb n1 hn1 => ?_))
  subst hb
  let a1 := a.set centerLocal (a.env 31)
  refine Hs.then (hs_sub C centerLocal centerBlocked a1 (by decide)
    (by simpa (config := { decide := true }) [a1, DS.set, hx, hready.blocked] using hxB))
    (fun b hb n2 hn2 => ?_)
  subst hb
  let a2 := a1.set centerLocal (a1.env centerLocal - a1.env centerBlocked)
  have hf : Fr a a2 [centerLocal] :=
    (Fr.set a _ (by simp)).trans (Fr.set a1 _ (by simp))
  have hlocal : a2.env centerLocal = x - P.r * P.b := by
    vsimp [a2, a1, hx, hready.blocked]
  refine Hs.last (centerFreeBit_spec a2 (hc.of_fr hf (by decide)) P row
    (x - P.r * P.b) 25 (by decide) ((hf _ (by decide)).trans hrow)
    hlocal (hready.local_frame hf) (by omega) hwidth) ?_
  rintro b ⟨hv, hsh, hfr⟩ n3 hn3
  exact ⟨⟨hv, hsh, (hf.weaken (by decide)).trans hfr⟩, by omega⟩

/-- `imp:pullback`, paper/paper.tex: the right free
tail subtracts both the coded boundary and left free-tail length. -/
def centerRightFree : St VV MM :=
  .seq (.op (.copy centerLocal 31))
    (.seq (.op (.sub centerLocal centerBlocked))
      (.seq (.op (.sub centerLocal centerFree)) (centerFreeBit 26)))

/-- `imp:pullback` and `prop:time`, paper/paper.tex: the right free-tail branch returns its literal column
bit with both original offsets physically subtracted. -/
theorem centerRightFree_spec {C : Ctx} (a : DS VV MM) (hc : Cst a)
    (P : StarParams) (column x : ℕ) (hcolumn : a.env 26 = column) (hx : a.env 31 = x)
    (hready : CenterReady a P) (hxF : P.r * P.b + PrimT.C4Geo.hL P ≤ x)
    (hxN : x < P.n) (hwidth : P.n + 4 ≤ C.Wd) :
    Hs C centerRightFree a (10 * P.n + 38) (fun b =>
      b.env centerOutput = (column.testBit
        (P.r / 2 * PrimT.C4Geo.dB P + (x - P.r * P.b - PrimT.C4Geo.hL P))).toNat ∧
      b.sh = a.sh ∧ Fr a b centerScratch) := by
  unfold centerRightFree
  refine Hx.hs (Hs.then (hs_copy C centerLocal 31 a (by decide))
    (fun b hb n1 hn1 => ?_))
  subst hb
  let a1 := a.set centerLocal (a.env 31)
  refine Hs.then (hs_sub C centerLocal centerBlocked a1 (by decide)
    (by simpa (config := { decide := true }) [a1, DS.set, hx, hready.blocked]
      using (show P.r * P.b ≤ x by omega))) (fun b hb n2 hn2 => ?_)
  subst hb
  let a2 := a1.set centerLocal (a1.env centerLocal - a1.env centerBlocked)
  refine Hs.then (hs_sub C centerLocal centerFree a2 (by decide)
    (by simpa (config := { decide := true }) [a2, a1, DS.set, hx, hready.blocked, hready.free]
      using (show PrimT.C4Geo.hL P ≤ x - P.r * P.b by omega))) (fun b hb n3 hn3 => ?_)
  subst hb
  let a3 := a2.set centerLocal (a2.env centerLocal - a2.env centerFree)
  have hf : Fr a a3 [centerLocal] :=
    (Fr.set a _ (by simp)).trans ((Fr.set a1 _ (by simp)).trans (Fr.set a2 _ (by simp)))
  have hlocal : a3.env centerLocal = x - P.r * P.b - PrimT.C4Geo.hL P := by
    vsimp [a3, a2, a1, hx, hready.blocked, hready.free]
  refine Hs.last (centerFreeBit_spec a3 (hc.of_fr hf (by decide)) P column
    (x - P.r * P.b - PrimT.C4Geo.hL P) 26 (by decide) ((hf _ (by decide)).trans hcolumn)
    hlocal (hready.local_frame hf) (by omega) hwidth) ?_
  rintro b ⟨hv, hsh, hfr⟩ n4 hn4
  exact ⟨⟨hv, hsh, (hf.weaken (by decide)).trans hfr⟩, by omega⟩

end NearQuarticWires.StageHamming
