import Proof.Quartic.StageMain.Call

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Dispatch NearCubicGates.Close.Interfaces

/-- `def:class`, `def:mask` and `prop:time`, paper/paper.tex: the original call is physically
traversed by its exact evaluator at the fixed all-zero input before
reading the compact structural indices that follow it. -/
def skipOriginalCall : St VV :=
  .seq (.op (.zero StageMain.pointSaved)) StageMain.scoreCall

/-- `def:mask` and `prop:time`, paper/paper.tex: an actual finite original call is consumed by a uniform
paid program; its scalar suffix is reached without a supplied parser
state, call-length oracle, gate values, or original incidence table. -/
theorem skipOriginalCall_spec {C : Ctx} (c : Call) (suffix : List Bool)
    (a : DS VV) (hc : Cst a) (hin : C.cw.drop a.cp = callWord c ++ suffix)
    (hW : C.cw.length + 4 ≤ C.Wd) (hn : c.n ≤ C.cw.length) :
    Hs C skipOriginalCall a (3000 * (C.cw.length + 2) ^ 3 + 2) (fun b =>
      b.cp = a.cp + (callWord c).length ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b) := by
  unfold skipOriginalCall
  refine Hx.hs (Hs.then (hs_zero C StageMain.pointSaved a) (fun b hb n1 hn1 => ?_))
  subst hb
  let a1 := a.set StageMain.pointSaved 0
  have hc1 : Cst a1 := hc.set _ _ (by decide)
  refine Hs.last (StageMain.scoreCall_spec c a1 hc1 suffix hin hW hn
    (by simp [a1])) ?_
  rintro b ⟨_, hbcp, hbwq, hbout, hbc, _⟩ n2 hn2
  exact ⟨⟨hbcp, hbwq, hbout, hbc⟩, by omega⟩

end NearQuarticWires.StageMainMask
