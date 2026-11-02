import Proof.Quartic.StagePullback.PointSetup

set_option autoImplicit false

namespace NearQuarticWires.StagePullback.Sides

open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicGates.Close.Cells

def leftEnd : Fin VV := 95
def blockedEnd : Fin VV := 96
def freeLeftEnd : Fin VV := 97
def result : Fin VV := 54

/-- `imp:partition` and `imp:pullback`, paper/paper.tex: compute the actual original-coordinate boundaries
of the left blocks, all blocks and the free left coordinates. -/
def boundsProgram : St VV MM :=
  .seq (.op (.mul Flips.halfCount 22 leftEnd))
    (.seq (.op (.mul 21 22 blockedEnd))
      (.seq (.op (.copy freeLeftEnd 20))
        (.seq (.op (.sub freeLeftEnd blockedEnd))
          (.seq (.op (.inc freeLeftEnd))
            (.seq (.op (.half freeLeftEnd)) (.op (.add freeLeftEnd blockedEnd)))))))

/-- `imp:pullback` and `prop:time`, paper/paper.tex: original scalar metadata physically determine all side
boundaries, including the asymmetric free-coordinate padding. -/
theorem boundsProgram_run (C : Ctx) (a : DS VV MM) (P : StarParams)
    (hn : a.env 20 = P.n) (hr : a.env 21 = P.r) (hb : a.env 22 = P.b)
    (hh : a.env Flips.halfCount = P.r / 2) (hwidth : P.n + 4 ≤ C.Wd) :
    Hs C boundsProgram a 13 (fun b =>
      b.env leftEnd = P.r / 2 * P.b ∧ b.env blockedEnd = P.r * P.b ∧
      b.env freeLeftEnd = P.r * P.b + (P.n - P.r * P.b + 1) / 2 ∧
      b.sh = a.sh ∧ Fr a b [leftEnd, blockedEnd, freeLeftEnd]) := by
  have hw := Flips.markerWidth C P hwidth
  have hl : P.r / 2 * P.b < 2 ^ C.Wd :=
    (Nat.mul_le_mul_right _ (Nat.div_le_self P.r 2)).trans_lt hw.2.1
  have hinc : P.n - P.r * P.b + 1 < 2 ^ C.Wd := by
    have hh : P.n + 1 < 2 ^ C.Wd :=
      (Nat.lt_two_pow_self (n := P.n + 1)).trans_le
        (Nat.pow_le_pow_right (by decide) (by omega))
    omega
  have hfree : (P.n - P.r * P.b + 1) / 2 + P.r * P.b < 2 ^ C.Wd := by
    have hh := PrimT.C4Geo.hL_le P
    unfold PrimT.C4Geo.hL at hh
    omega
  unfold boundsProgram
  refine Hx.hs (Hs.then (hs_mul C Flips.halfCount 22 leftEnd a (by decide) (by decide) (by decide)
    (by rw [hh, hb]; exact hl)) (fun b he n1 hn1 => ?_))
  subst he
  refine Hs.then (hs_mul C 21 22 blockedEnd _ (by decide) (by decide) (by decide)
    (by vsimp [hr, hb]; exact hw.2.1)) (fun b he n2 hn2 => ?_)
  subst he
  refine Hs.then (hs_copy C freeLeftEnd 20 _ (by decide)) (fun b he n3 hn3 => ?_)
  subst he
  refine Hs.then (hs_sub C freeLeftEnd blockedEnd _ (by decide)
    (by vsimp [hn, hr, hb]; exact P.r_mul_b_le)) (fun b he n4 hn4 => ?_)
  subst he
  refine Hs.then (hs_inc C freeLeftEnd _ (by vsimp [hn, hr, hb]; exact hinc))
    (fun b he n5 hn5 => ?_)
  subst he
  refine Hs.then (hs_half C freeLeftEnd _) (fun b he n6 hn6 => ?_)
  subst he
  refine Hs.last (hs_add C freeLeftEnd blockedEnd _ (by decide)
    (by vsimp [hn, hr, hb]; exact hfree)) ?_
  rintro b he n7 hn7
  subst he
  refine ⟨⟨?_, ?_, ?_, rfl, ?_⟩, by omega⟩
  · vsimp [hh, hb]
  · vsimp [hr, hb]
  · vsimp [hn, hr, hb, Nat.add_comm]
  · exact (Fr.set a _ (by simp)).trans
      ((Fr.set _ _ (by simp)).trans ((Fr.set _ _ (by simp)).trans
        ((Fr.set _ _ (by simp)).trans ((Fr.set _ _ (by simp)).trans
          ((Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp)))))))

/-- `imp:pullback`, paper/paper.tex: compare the
original coordinate with the three physically computed side boundaries. -/
def program : St VV MM :=
  .ite (.lt MarkerCalls.originalCoordinate leftEnd) (.op (.copy result v1))
    (.ite (.lt MarkerCalls.originalCoordinate blockedEnd) (.op (.zero result))
      (.ite (.lt MarkerCalls.originalCoordinate freeLeftEnd) (.op (.copy result v1))
        (.op (.zero result))))

/-- `imp:pullback` and `prop:time`, paper/paper.tex: the actual side program returns the canonical original
coordinate's left/right placement, rather than an arbitrary supplied map. -/
theorem program_run (C : Ctx) (a : DS VV MM) (P : StarParams) (x : Fin P.n)
    (hc : Cst a) (hx : a.env MarkerCalls.originalCoordinate = x.val)
    (hl : a.env leftEnd = P.r / 2 * P.b) (hb : a.env blockedEnd = P.r * P.b)
    (hf : a.env freeLeftEnd = P.r * P.b + (P.n - P.r * P.b + 1) / 2) :
    Hs C program a 4 (fun b => b.env result = (P.centerSide x).toNat ∧
      b.sh = a.sh ∧ Fr a b [result]) := by
  unfold program
  by_cases hleft : x.val < P.r / 2 * P.b
  · refine Hs.mono (Hs.iteT (show MarkerCalls.originalCoordinate ≠ leftEnd by decide)
      (by simp [Cnd.eval, hx, hl, hleft]) (hs_copy C result v1 a (by decide))) (by omega) ?_
    rintro b rfl
    exact ⟨by simp [hc.one, StarParams.centerSide, hleft], rfl, Fr.set a _ (by simp)⟩
  · refine Hs.iteF (show MarkerCalls.originalCoordinate ≠ leftEnd by decide)
      (by simp [Cnd.eval, hx, hl, hleft]) ?_
    by_cases hblock : x.val < P.r * P.b
    · refine Hs.mono (Hs.iteT (show MarkerCalls.originalCoordinate ≠ blockedEnd by decide)
        (by simp [Cnd.eval, hx, hb, hblock]) (hs_zero C result a)) (by omega) ?_
      rintro b rfl
      exact ⟨by simp [StarParams.centerSide, hleft, show ¬ P.r * P.b ≤ x.val by omega],
        rfl, Fr.set a _ (by simp)⟩
    · refine Hs.iteF (show MarkerCalls.originalCoordinate ≠ blockedEnd by decide)
        (by simp [Cnd.eval, hx, hb, hblock]) ?_
      by_cases hfree : x.val < P.r * P.b + (P.n - P.r * P.b + 1) / 2
      · refine Hs.mono (Hs.iteT (show MarkerCalls.originalCoordinate ≠ freeLeftEnd by decide)
          (by simp [Cnd.eval, hx, hf, hfree]) (hs_copy C result v1 a (by decide))) le_rfl ?_
        rintro b rfl
        exact ⟨by simp [hc.one, StarParams.centerSide, hleft, hfree,
          show P.r * P.b ≤ x.val by omega], rfl, Fr.set a _ (by simp)⟩
      · refine Hs.mono (Hs.iteF (show MarkerCalls.originalCoordinate ≠ freeLeftEnd by decide)
          (by simp [Cnd.eval, hx, hf, hfree]) (hs_zero C result a)) le_rfl ?_
        rintro b rfl
        exact ⟨by simp [StarParams.centerSide, hleft, hfree], rfl, Fr.set a _ (by simp)⟩

end NearQuarticWires.StagePullback.Sides
