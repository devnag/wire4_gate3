import Proof.Quartic.StageModularCuts.RowData
import Proof.Quartic.StageModularCuts.AffineCopy
import Proof.Quartic.StageModularCuts.Flow

set_option autoImplicit false

namespace NearQuarticWires.StageModularCuts

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Recovery.HTParts

/-- `lem:print`, paper/paper.tex: one actual weak cut
copies its affine fields and then reduces its final signed coefficient. -/
def rowProgram : Program := .seq copyAffine transferCoefficient

def rowCost (p width : ℕ) : ℕ :=
  55 * ((2 * width + 1) * (2 * p + 3)) + 22 * (2 * width + 1) + 6 + transferCost p

/-- `lem:print` and `prop:time`, paper/paper.tex: the complete row pass uses actual stream bytes and restores
all loop parameters, with a fixed polynomial cost in field and dense widths. -/
theorem rowProgram_spec (cap p q width : ℕ) (c : MatrixScoreBatch.Cut)
    (pre suffix : List Bool) (a : State) (hw : Workspace a p q)
    (hq : 0 < q) (hfit : q ≤ 2 ^ p) (hz : c.coefficient.natAbs < 2 ^ p)
    (hl : c.leftWeights.length = width) (hr : c.rightWeights.length = width)
    (hsource : a.st 3 = pre ++ MatrixScoreBatch.cutWord p c ++ suffix)
    (hhead : a.sh 3 = pre.length) (hSC : a.val 5 = pre.length)
    (hout : a.sh 14 = (a.st 14).length) (hstride : a.val 8 = 2 * width + 1)
    (hK : a.val 9 = 0) (hCW : a.val 10 = 0) (hT : a.val 12 = 0)
    (hsourceCap : pre.length + (MatrixScoreBatch.cutWord p c).length + 1 ≤ cap)
    (houtCap : a.val 6 + 2 * (MatrixScoreBatch.cutWord p c).length + 1 ≤ cap)
    (hcountCap : 2 * width + 1 ≤ cap) :
    ∃ b, WXExec cap rowProgram a b (rowCost p width) ∧ Workspace b p q ∧
      Flow a b (MatrixScoreBatch.cutWord p c).length
        (marks (MatrixScoreBatch.cutWord p (StageRecovery.reduceCut q c))) := by
  have hfields : (affineFields p c).length = 2 * width + 1 := by
    rw [affineFields_length, hl, hr]; omega
  have hbytes : (affineWord p c).length = (2 * width + 1) * (2 * p + 3) := by
    rw [affineWord_length, hl, hr]; ring
  have htotal : (MatrixScoreBatch.cutWord p c).length = (affineWord p c).length + (2 * p + 3) := by
    rw [cutWord_split, List.length_append, frame_length, MatrixScoreBatch.signMagnitude_length]
    omega
  have e1 := copyAffine_spec cap (affineFields p c) pre
    (frame (MatrixScoreBatch.signMagnitude p c.coefficient) ++ suffix) a
    (by rw [hsource, cutWord_split]; simp only [affineWord, List.append_assoc])
    hhead hout (by rw [hfields]; exact hstride) hK hT
    (by change a.val 6 + 2 * (affineWord p c).length ≤ cap; rw [htotal] at houtCap; omega)
    (by change a.val 5 + (affineWord p c).length ≤ cap
        have hbound := hsourceCap
        rw [htotal] at hbound
        rw [hSC]
        omega)
    (by rw [hfields]; exact hcountCap)
  let b := adv 3 14 6 5 a (marks (affineWord p c)) (affineWord p c).length
  have hbworkspace : Workspace b p q := hw.advance _ _
  have hf1 : Flow a b (affineWord p c).length (marks (affineWord p c)) := flow_adv a _ _
  have hbsource : b.st 3 = (pre ++ affineWord p c) ++
      frame (MatrixScoreBatch.signMagnitude p c.coefficient) ++ suffix := by
    rw [hf1.source, hsource, cutWord_split]
    simp only [List.append_assoc]
  have hbhead : b.sh 3 = (pre ++ affineWord p c).length := by
    rw [hf1.head, hhead, List.length_append]
  have hbSC : b.val 5 = (pre ++ affineWord p c).length := by
    rw [hf1.count, hSC, List.length_append]
  have hbCW : b.val 10 = 0 := (hf1.registers 10 (by decide) (by decide)).trans hCW
  have hbout : b.sh 14 = (b.st 14).length := by
    rw [hf1.outputHead, hf1.output, List.length_append, hout]
  have e2 := transferCoefficient_spec cap p q c.coefficient (pre ++ affineWord p c) suffix b
    hbworkspace hq hfit hz hbsource hbhead hbSC hbCW hbout
    (by rw [List.length_append]
        have hbound := hsourceCap
        rw [htotal] at hbound
        omega)
    (by rw [hf1.outputCount, Streaming.marks_length]; rw [htotal] at houtCap; omega)
  have hf2 := transferFinal_flow hbworkspace c.coefficient (hbhead.trans hbSC.symm)
  rw [hbSC] at hf2
  have hf := hf1.trans hf2
  have hemit : marks (affineWord p c) ++
      marks (frame (MatrixScoreBatch.signMagnitude p (c.coefficient % (q : ℤ)))) =
      marks (MatrixScoreBatch.cutWord p (StageRecovery.reduceCut q c)) := by
    rw [reducedWord_split, Streaming.marks_append]
  rw [← htotal, hemit] at hf
  refine ⟨_, ?_, transferFinal_workspace hbworkspace c.coefficient _, hf⟩
  refine (WXExec.seq e1 e2).mono ?_
  change 55 * (affineWord p c).length + 22 * (affineFields p c).length + 5 + 1 + transferCost p ≤ _
  rw [hbytes, hfields]
  unfold rowCost
  omega

end NearQuarticWires.StageModularCuts
