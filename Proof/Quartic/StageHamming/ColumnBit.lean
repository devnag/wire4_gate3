import Proof.Quartic.StageHamming.ColumnLoop

set_option autoImplicit false

namespace NearQuarticWires.StageHamming

open NearCubicGates.Close.Cells
open NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.Shared

def columnBitScratch : List (Fin VV) := bitInput :: paritySuccessor :: columnLoopScratch

/-- `imp:partition`, paper/paper.tex: the complete
physical basis-column bit initializes its data bit reader, target,
power, and equality contribution before scanning the parity checks. -/
def columnBit : St VV MM :=
  .seq (.op (.copy bitInput columnData))
    (.seq (.op (.inc bitInput))
      (.seq (.op (.copy paritySuccessor columnTarget))
        (.seq (.op (.inc paritySuccessor))
          (.seq (.op (.copy parityPower v1))
            (.seq columnInitialFlag columnLoop)))))

/-- `imp:partition` and `prop:time`, paper/paper.tex: the complete canonical column bit is computed from its
three scalar arguments, including all physical initialization costs. -/
theorem columnBit_spec {C : Ctx} (a : DS VV MM) (hc : Cst a)
    (i q s : ℕ) (hi : a.env columnData = i) (hq : a.env columnTarget = q)
    (hswidth : a.env parityWidth = s)
    (hiW : i + 1 < 2 ^ C.Wd) (hqW : q + 1 < 2 ^ C.Wd)
    (hs : s < 2 ^ C.Wd) (hwidth : 2 ≤ C.Wd) (hW : 2 ^ s < 2 ^ C.Wd) :
    Hs C columnBit a (s * (5 * s + 21) + 24) (fun b =>
      b.env columnOutput = (columnPrefix i q s).toNat ∧
      b.sh = a.sh ∧ Fr a b columnBitScratch) := by
  unfold columnBit
  refine Hx.hs (Hs.then (hs_copy C bitInput columnData a (by decide))
    (fun b hb n1 hn1 => ?_))
  subst hb
  let a1 := a.set bitInput (a.env columnData)
  refine Hs.then (hs_inc C bitInput a1 (by rw [DS.set_env_self, hi]; exact hiW))
    (fun b hb n2 hn2 => ?_)
  subst hb
  let a2 := a1.set bitInput (a1.env bitInput + 1)
  refine Hs.then (hs_copy C paritySuccessor columnTarget a2 (by decide))
    (fun b hb n3 hn3 => ?_)
  subst hb
  let a3 := a2.set paritySuccessor (a2.env columnTarget)
  have ha3q : a3.env paritySuccessor = q := by vsimp [a3, a2, a1, hq]
  refine Hs.then (hs_inc C paritySuccessor a3 (by rw [ha3q]; exact hqW))
    (fun b hb n4 hn4 => ?_)
  subst hb
  let a4 := a3.set paritySuccessor (a3.env paritySuccessor + 1)
  refine Hs.then (hs_copy C parityPower v1 a4 (by decide))
    (fun b hb n5 hn5 => ?_)
  subst hb
  let a5 := a4.set parityPower (a4.env v1)
  have hf5 : Fr a a5 columnBitScratch :=
    (Fr.set a _ (by decide)).trans ((Fr.set a1 _ (by decide)).trans
      ((Fr.set a2 _ (by decide)).trans ((Fr.set a3 _ (by decide)).trans
        (Fr.set a4 _ (by decide)))))
  have hc5 : Cst a5 := hc.of_fr hf5 (by decide)
  have hi5 : a5.env bitInput = i + 1 := by vsimp [a5, a4, a3, a2, a1, hi]
  have hq5 : a5.env paritySuccessor = q + 1 := by vsimp [a5, a4, ha3q]
  have hp5 : a5.env parityPower = 1 := by vsimp [a5, a4, a3, a2, a1, hc.one]
  refine Hs.then (columnInitialFlag_spec a5 hc5 i q
    ((hf5 _ (by decide)).trans hi) ((hf5 _ (by decide)).trans hq))
    (fun b hb n6 hn6 => ?_)
  obtain ⟨hbflag, hbsh, hbfr⟩ := hb
  have hfb : Fr a b columnBitScratch := hf5.trans (hbfr.weaken (by decide))
  have hcb : Cst b := hc.of_fr hfb (by decide)
  refine Hs.last (columnLoop_spec b hcb i q s
    ((hbfr _ (by decide)).trans hi5) ((hbfr _ (by decide)).trans hq5)
    ((hfb _ (by decide)).trans hswidth) ((hbfr _ (by decide)).trans hp5)
    hbflag hs hwidth hW) ?_
  rintro c ⟨_, hcflag, hcsh, hcfr⟩ n7 hn7
  exact ⟨⟨hcflag, hcsh.trans hbsh, hfb.trans (hcfr.weaken (by decide))⟩, by omega⟩

/-- `imp:partition`, paper/paper.tex: the physical
scalar result agrees with the original canonical Hamming basis bit. -/
theorem columnBit_cwBit_spec {C : Ctx} (a : DS VV MM) (hc : Cst a)
    (P : StarParams) (i q : ℕ) (hi : a.env columnData = i)
    (hq : a.env columnTarget = q) (hswidth : a.env parityWidth = P.s)
    (hiW : i + 1 < 2 ^ C.Wd) (hqW : q + 1 < 2 ^ C.Wd)
    (hs : P.s < 2 ^ C.Wd) (hwidth : 2 ≤ C.Wd) (hW : 2 ^ P.s < 2 ^ C.Wd) :
    Hs C columnBit a (P.s * (5 * P.s + 21) + 24) (fun b =>
      b.env columnOutput = (PrimT.C4Geo.cwBit P i q).toNat ∧
      b.sh = a.sh ∧ Fr a b columnBitScratch) :=
  columnBit_spec a hc i q P.s hi hq hswidth hiW hqW hs hwidth hW

end NearQuarticWires.StageHamming
