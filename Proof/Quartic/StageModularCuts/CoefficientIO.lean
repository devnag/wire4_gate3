import Proof.Quartic.StageModularCuts.Workspace
import Proof.Quartic.StagePrintTuple.MarkedFrame

set_option autoImplicit false

namespace NearQuarticWires.StageModularCuts

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close.WordPrograms

/-- `lem:print`, paper/paper.tex: a signed coefficient
is physically read from the row stream, reduced, and emitted with the
original fixed width inside the outer result frame. -/
def transferCoefficient : Program :=
  .seq (.wm (copyRec 3 coefficient 5 10))
    (.seq coefficientProgram (.wm (StageTuple.appendMarkedFrameReset coefficient 14 6 10)))

def transferFinal (a : State) (p : ℕ) (z : ℤ) (q position : ℕ) : State :=
  appendO (coefficientFinal
    (atRec 3 coefficient 5 a (MatrixScoreBatch.signMagnitude p z) position) p z q)
    14 6 (marks (frame (MatrixScoreBatch.signMagnitude p (z % (q : ℤ)))))

def transferCost (p : ℕ) : ℕ := 40 * (p + 1) + 24 + coefficientCost p + 100 * (2 * p + 4)

/-- `lem:print` and `prop:time`, paper/paper.tex: the coefficient transfer includes its actual frame read,
binary modular arithmetic, framed output, and scratch-head restoration. -/
theorem transferCoefficient_spec (cap p q : ℕ) (z : ℤ) (pre suffix : List Bool) (a : State)
    (hw : Workspace a p q) (hq : 0 < q) (hfit : q ≤ 2 ^ p)
    (hz : z.natAbs < 2 ^ p)
    (hsource : a.st 3 = pre ++ frame (MatrixScoreBatch.signMagnitude p z) ++ suffix)
    (hhead : a.sh 3 = pre.length) (hSC : a.val 5 = pre.length)
    (hCW : a.val 10 = 0) (hout : a.sh 14 = (a.st 14).length)
    (hsourceCap : pre.length + (2 * p + 3) + 1 ≤ cap)
    (houtCap : a.val 6 + 2 * (2 * p + 3) + 1 ≤ cap) :
    WXExec cap transferCoefficient a (transferFinal a p z q (pre.length + (2 * p + 3)))
      (transferCost p) := by
  let w := MatrixScoreBatch.signMagnitude p z
  have hwl : w.length = p + 1 := MatrixScoreBatch.signMagnitude_length p z
  have e1 := copyRec_spec cap (by decide : (3 : Fin 16) ≠ coefficient)
    (by decide : (5 : Fin 16) ≠ 10) a pre w suffix
    (by rw [hsource, frame_eq_frameP]; simp only [List.append_assoc, List.singleton_append]; rfl)
    hhead hSC hw.head hCW (by rw [hwl]; exact hw.length) (by rw [hwl]; omega)
  have hpos : pre.length + 2 * w.length + 1 = pre.length + (2 * p + 3) := by rw [hwl]; omega
  rw [hpos] at e1
  let b := atRec 3 coefficient 5 a w (pre.length + (2 * p + 3))
  have hwb : Workspace b p q := hw.read z _
  obtain ⟨x, u, v, t, hbwords⟩ := hwb.words
  have hzb : SInt.SNumOn b coefficient p z := by
    refine ⟨⟨?_, hwb.head⟩, hz⟩
    simp only [b, atRec, WState.setv_st, WState.seth_st, WState.sets_st,
      Function.update_self, w, SInt.signMagnitude_eq]
  have e2 := coefficientProgram_spec cap p b z q x u v t hzb hbwords hwb.clear hwb.sign hq hfit
    (by omega)
  let c := coefficientFinal b p z q
  have hcword := coefficientFinal_word b p z q
  have hcframe := coefficientFinal_frame b p z q hwb.sign
  have hcout : c.sh 14 = (c.st 14).length := by
    rw [hcframe.sh (by decide), hcframe.st (by decide)]
    simpa [b, atRec, coefficient] using hout
  have hcCW : c.val 10 = 0 := by
    rw [coefficientFinal_registers b p z q hwb.sign]
    simpa [b, atRec] using hCW
  have hcOP : c.val 6 = a.val 6 := by
    rw [coefficientFinal_registers b p z q hwb.sign]
    simp [b, atRec]
  have e3 := StageTuple.appendMarkedFrameReset_spec cap coefficient 14 6 10
    (by decide) (by decide) (MatrixScoreBatch.signMagnitude p (z % (q : ℤ))) [] c
    (by simpa only [List.append_nil] using hcword)
    (by rw [coefficientFinal_heads]; exact hwb.head) hcout hcCW
    (by rw [hcOP, frame_length, MatrixScoreBatch.signMagnitude_length]; omega)
  refine WXExec.seq' cap (WXExec.wm e1) (WXExec.seq e2 (WXExec.wm e3)) ?_
  rw [hwl]
  unfold transferCost StageTuple.appendMarkedFrameCost
  rw [frame_length, MatrixScoreBatch.signMagnitude_length]
  omega

end NearQuarticWires.StageModularCuts
