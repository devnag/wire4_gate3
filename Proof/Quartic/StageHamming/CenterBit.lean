import Proof.Quartic.StageHamming.CenterCases

set_option autoImplicit false

namespace NearQuarticWires.StageHamming

open NearCubicGates.Close.Cells
open NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.Shared

/-- `imp:partition` and `imp:pullback`, paper/paper.tex: the four literal original-coordinate cases
select the canonical left/right block or free-tail computation. -/
def centerBranches : St VV MM :=
  .ite (.lt 31 centerLeft) centerLeftBlock
    (.ite (.lt 31 centerBlocked) centerRightBlock
      (.ite (.lt 31 centerOutput) centerLeftFree centerRightFree))

/-- `imp:partition`, `imp:pullback` and `prop:time`, paper/paper.tex: the four physical branches
return the exact canonical center bit, with every scalar cost paid. -/
theorem centerBranches_spec {C : Ctx} (a : DS VV MM) (hc : Cst a)
    (P : StarParams) (row column x : ℕ)
    (hrow : a.env 25 = row) (hcolumn : a.env 26 = column) (hx : a.env 31 = x)
    (hready : CenterReady a P) (hxN : x < P.n) (hwidth : P.n + 4 ≤ C.Wd) :
    Hs C centerBranches a (200 * (P.n + 1) ^ 3 + 50) (fun b =>
      b.env centerOutput = (PrimT.C4Geo.ctrBit P row column x).toNat ∧
      b.sh = a.sh ∧ Fr a b centerScratch) := by
  have hn : P.n ≤ (P.n + 1) ^ 3 := by
    have hp : P.n + 1 ≤ (P.n + 1) ^ 3 := by
      simpa only [pow_one] using
        Nat.pow_le_pow_right (Nat.succ_pos P.n) (by decide : 1 ≤ 3)
    exact (Nat.le_succ P.n).trans hp
  unfold centerBranches
  refine Hs.mono (Hs.ite (t := 200 * (P.n + 1) ^ 3 + 42)
    (show (31 : Fin VV) ≠ centerLeft by decide) ?_ ?_) (by omega) (fun _ h => h)
  · intro he
    have hxL : x < P.r / 2 * P.b := by
      simpa only [Cnd.eval, hx, hready.left, decide_eq_true_eq] using he
    exact (centerLeftBlock_spec a hc P row x hrow hx hready hxL hwidth).mono
      (by omega) (fun _ h => by simpa only [PrimT.C4Geo.ctrBit, if_pos hxL] using h)
  · intro he
    have hxL : ¬ x < P.r / 2 * P.b := by
      simpa only [Cnd.eval, hx, hready.left, decide_eq_false_iff_not] using he
    refine Hs.ite (t := 200 * (P.n + 1) ^ 3 + 41)
      (show (31 : Fin VV) ≠ centerBlocked by decide) ?_ ?_
    · intro hb
      have hxB : x < P.r * P.b := by
        simpa only [Cnd.eval, hx, hready.blocked, decide_eq_true_eq] using hb
      exact (centerRightBlock_spec a hc P column x hcolumn hx hready (by omega) hxB hwidth).mono
        (by omega) (fun _ h => by
          simpa only [PrimT.C4Geo.ctrBit, if_neg hxL, if_pos hxB] using h)
    · intro hb
      have hxB : ¬ x < P.r * P.b := by
        simpa only [Cnd.eval, hx, hready.blocked, decide_eq_false_iff_not] using hb
      refine Hs.ite (t := 200 * (P.n + 1) ^ 3 + 40)
        (show (31 : Fin VV) ≠ centerOutput by decide) ?_ ?_
      · intro hf
        have hxF : x < P.r * P.b + PrimT.C4Geo.hL P := by
          simpa only [Cnd.eval, hx, hready.upper, decide_eq_true_eq] using hf
        exact (centerLeftFree_spec a hc P row x hrow hx hready (by omega) hxN hwidth).mono
          (by omega) (fun _ h => by
            simpa only [PrimT.C4Geo.ctrBit, if_neg hxL, if_neg hxB, if_pos hxF] using h)
      · intro hf
        have hxF : ¬ x < P.r * P.b + PrimT.C4Geo.hL P := by
          simpa only [Cnd.eval, hx, hready.upper, decide_eq_false_iff_not] using hf
        exact (centerRightFree_spec a hc P column x hcolumn hx hready (by omega) hxN hwidth).mono
          (by omega) (fun _ h => by
            simpa only [PrimT.C4Geo.ctrBit, if_neg hxL, if_neg hxB, if_neg hxF] using h)

/-- `imp:partition` and `imp:pullback`, paper/paper.tex: the complete inline original center-bit program
first computes its actual metadata and then executes the four cases. -/
def centerBit : St VV MM := .seq centerMetadata centerBranches

/-- `imp:partition`, `imp:pullback` and `prop:time`, paper/paper.tex: the actual original point
metadata computes its canonical center bit in a fixed cubic source
clock, preserving the caller's original fields, flips and corner bits. -/
theorem centerBit_spec {C : Ctx} (a : DS VV MM) (hc : Cst a)
    (P : StarParams) (row column x : ℕ)
    (hn : a.env 20 = P.n) (hr : a.env 21 = P.r)
    (hb : a.env 22 = P.b) (hs : a.env 23 = P.s)
    (hrow : a.env 25 = row) (hcolumn : a.env 26 = column) (hx : a.env 31 = x)
    (hxN : x < P.n) (hwidth : P.n + 4 ≤ C.Wd) :
    Hs C centerBit a (300 * (P.n + 1) ^ 3) (fun b =>
      b.env centerOutput = (PrimT.C4Geo.ctrBit P row column x).toNat ∧
      b.sh = a.sh ∧ Fr a b centerScratch) := by
  unfold centerBit
  refine Hx.hs (Hs.then (centerMetadata_spec a P hn hr hb hs hwidth)
    (fun b hbp n1 hn1 => ?_))
  obtain ⟨hready, hbsh, hbfr⟩ := hbp
  have hcb : Cst b := hc.of_fr hbfr (by decide)
  refine Hs.last (centerBranches_spec b hcb P row column x
    ((hbfr _ (by decide)).trans hrow) ((hbfr _ (by decide)).trans hcolumn)
    ((hbfr _ (by decide)).trans hx) hready hxN hwidth) ?_
  rintro c ⟨hcvalue, hcsh, hcfr⟩ n2 hn2
  have hpow : 1 ≤ (P.n + 1) ^ 3 := Nat.one_le_pow _ _ (Nat.succ_pos _)
  exact ⟨⟨hcvalue, hcsh.trans hbsh, (hbfr.weaken (by decide)).trans hcfr⟩, by omega⟩

end NearQuarticWires.StageHamming
