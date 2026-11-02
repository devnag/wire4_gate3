import Proof.Quartic.StageMain.PackedPoint
import Proof.Gates.Dispatch.Arith2

/-!
# Reading a specified coordinate of a packed sample

Paper: `def:class`, paper/paper.tex, and Step 4 of
`sec:algorithm`. Binary shifts construct the coordinate
power, division selects its suffix, and the low-bit remainder is the
requested input bit. The selected coordinate lies within the allocated
binary width.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain

open NearCubicGates.Close.Dispatch
open StageOutput

def pointQuotientAssignments : List Assignment := [(pointWork, .div (.var pointSaved) (.var P2X))]
def readPointBit : St VV := .seq (.op (.copy P2E t3))
  (.seq pow2v (.seq (assignmentProgram pointQuotientAssignments) nextPointBit))
def readPointBitScratch : List (Fin VV) := [P2E, P2X, P2I, vJ, pointWork, pointBit]

theorem pointQuotientAssignments_legal : assignmentsLegal pointQuotientAssignments := by
  simp (config := { decide := true }) [assignmentsLegal, pointQuotientAssignments, AE.vars_ok,
    pointWork, pointSaved, P2X, vZ, v1, v2, vPOS, VV]

theorem readPointBit_spec {C : Ctx} (a : DS VV) (hc : Cst a) (i : ℕ)
    (hi : a.env t3 = i) (hW : i + 2 ≤ C.Wd) (hpoint : a.env pointSaved < 2 ^ C.Wd) :
    Hs C readPointBit a (5 * i + 80) (fun b =>
      b.env pointBit = ((a.env pointSaved).testBit i).toNat ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ FrS a b readPointBitScratch) := by
  refine Hx.hs (Hs.then (hs_copy C P2E t3 a (by decide)) (fun b hb n1 hn1 => ?_))
  subst hb
  refine Hs.then (pow2v_spec _ (hc.set _ _ (by decide)) i (by simpa using hi) (by omega))
    (fun c ⟨cx, cp, cw, co, cc, cf⟩ n2 hn2 => ?_)
  have cpoint : c.env pointSaved = a.env pointSaved := by
    rw [cf _ (by decide), DS.set_env_ne _ _ (by decide)]
  have htwo : 2 * 2 ^ i ≤ 2 ^ C.Wd := by
    rw [← pow_succ']
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have csafe : assignmentsSafe C.Wd pointQuotientAssignments c.env := by
    simp [assignmentsSafe, pointQuotientAssignments, AE.ok, AE.eval, cx, htwo]
  refine Hs.then (assignmentProgram_spec pointQuotientAssignments pointQuotientAssignments_legal c cc csafe)
    (fun d ⟨de, dp, dw, dout, dc⟩ n3 hn3 => ?_)
  have dx : d.env pointWork = a.env pointSaved / 2 ^ i := by
    rw [de pointWork (by decide) (by decide)]
    simp [assignmentEnv, pointQuotientAssignments, AE.eval, cx, cpoint]
  have df := assignmentProgram_frame de
  refine Hs.last (nextPointBit_spec d dc (by omega) (by
    rw [dx]; exact (Nat.div_le_self _ _).trans_lt hpoint)) ?_
  rintro e ⟨eb, _, ep, ew, eo, ec, ef⟩ n4 hn4
  refine ⟨⟨?_, by simpa using ep.trans (dp.trans cp), by simpa using ew.trans (dw.trans cw),
    by simpa using eo.trans (dout.trans co), ec,
    FrS.trans (Fr.set _ (x := P2E) _ (by decide)).toS
      (FrS.trans (cf.toS.weaken (by decide)) (FrS.trans (df.weaken (by decide)) (ef.weaken (by decide))))⟩, ?_⟩
  · rw [eb, dx, Nat.testBit_eq_decide_div_mod_eq]
    rcases Nat.mod_two_eq_zero_or_one (a.env pointSaved / 2 ^ i) with hz | ho
    · simp [hz]
    · simp [ho]
  · have hh : assignmentCost pointQuotientAssignments ≤ 20 := by decide
    omega

end NearQuarticWires.StageMain
