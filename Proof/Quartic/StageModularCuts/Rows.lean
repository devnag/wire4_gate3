import Proof.Quartic.StageModularCuts.Row

set_option autoImplicit false

namespace NearQuarticWires.StageModularCuts

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.CheckedPCPP.LitDecode (rtb_off0)

/-- `lem:print`, paper/paper.tex: the row loop stops
at the actual end of the raw weak-cut stream. -/
def rowsProgram : Program := .whs 3 rowProgram

/-- `lem:print` and `prop:time`, paper/paper.tex: the complete stream pass preserves row order and every
affine byte, reduces each signed coefficient, and charges one bounded
binary reduction per actual row. The empty stream executes no row. -/
theorem rowsProgram_spec (cap p q width : ℕ) (cuts : List MatrixScoreBatch.Cut)
    (pre : List Bool) (a : State) (hw : Workspace a p q)
    (hq : 0 < q) (hfit : q ≤ 2 ^ p)
    (hcuts : ∀ c ∈ cuts, c.leftWeights.length = width ∧ c.rightWeights.length = width ∧
      c.coefficient.natAbs < 2 ^ p)
    (hsource : a.st 3 = pre ++ cuts.flatMap (MatrixScoreBatch.cutWord p))
    (hhead : a.sh 3 = pre.length) (hSC : a.val 5 = pre.length)
    (hout : a.sh 14 = (a.st 14).length) (hstride : a.val 8 = 2 * width + 1)
    (hK : a.val 9 = 0) (hCW : a.val 10 = 0) (hT : a.val 12 = 0)
    (hsourceCap : pre.length + (cuts.flatMap (MatrixScoreBatch.cutWord p)).length + 1 ≤ cap)
    (houtCap : a.val 6 + 2 * (cuts.flatMap (MatrixScoreBatch.cutWord p)).length + 1 ≤ cap)
    (hcountCap : 2 * width + 1 ≤ cap) :
    ∃ b, WXExec cap rowsProgram a b (cuts.length * (rowCost p width + 2) + 1) ∧
      Workspace b p q ∧ Flow a b (cuts.flatMap (MatrixScoreBatch.cutWord p)).length
        (marks ((cuts.map (StageRecovery.reduceCut q)).flatMap (MatrixScoreBatch.cutWord p))) := by
  induction cuts generalizing pre a with
  | nil =>
      simp only [List.length_nil, List.flatMap_nil, List.map_nil, marks, Nat.zero_mul, Nat.zero_add]
      refine ⟨a, ?_, hw, ?_⟩
      · apply WXExec.whsF
        unfold wbit
        rw [hsource, hhead]
        simp [readTapeBit]
      · constructor
        · rfl
        · simp
        · simp
        · simp
        · simp
        · simp
        · intro j _ _; rfl
  | cons c cs ih =>
      obtain ⟨hl, hr, hz⟩ := hcuts c (by simp)
      have hbytes : ((c :: cs).flatMap (MatrixScoreBatch.cutWord p)).length =
          (MatrixScoreBatch.cutWord p c).length + (cs.flatMap (MatrixScoreBatch.cutWord p)).length := by simp
      have hbit : wbit a 3 = true := by
        unfold wbit
        rw [hsource, hhead]
        simp only [List.flatMap_cons, rtb_off0]
        have he : ∀ bits : List Bool, readTapeBit bits 0 = bits.headD false := by
          intro bits; cases bits <;> rfl
        rw [he]
        exact cutWord_head p c _
      obtain ⟨b, e1, hwb, hf1⟩ := rowProgram_spec cap p q width c pre
        (cs.flatMap (MatrixScoreBatch.cutWord p)) a hw hq hfit hz hl hr
        (by simpa only [List.flatMap_cons, List.append_assoc] using hsource)
        hhead hSC hout hstride hK hCW hT
        (by rw [hbytes] at hsourceCap; omega)
        (by rw [hbytes] at houtCap; omega) hcountCap
      have hbsource : b.st 3 = (pre ++ MatrixScoreBatch.cutWord p c) ++
          cs.flatMap (MatrixScoreBatch.cutWord p) := by
        rw [hf1.source, hsource]
        simp only [List.flatMap_cons, List.append_assoc]
      have hbhead : b.sh 3 = (pre ++ MatrixScoreBatch.cutWord p c).length := by
        rw [hf1.head, hhead, List.length_append]
      have hbSC : b.val 5 = (pre ++ MatrixScoreBatch.cutWord p c).length := by
        rw [hf1.count, hSC, List.length_append]
      have hbout : b.sh 14 = (b.st 14).length := by
        rw [hf1.outputHead, hf1.output, List.length_append, hout]
      have hredlen : (MatrixScoreBatch.cutWord p (StageRecovery.reduceCut q c)).length =
          (MatrixScoreBatch.cutWord p c).length := by
        simp only [cutWord_length, StageRecovery.reduceCut]
      obtain ⟨d, e2, hwd, hf2⟩ := ih (pre ++ MatrixScoreBatch.cutWord p c) b hwb
        (fun x hx => hcuts x (List.mem_cons_of_mem c hx)) hbsource hbhead hbSC hbout
        ((hf1.registers 8 (by decide) (by decide)).trans hstride)
        ((hf1.registers 9 (by decide) (by decide)).trans hK)
        ((hf1.registers 10 (by decide) (by decide)).trans hCW)
        ((hf1.registers 12 (by decide) (by decide)).trans hT)
        (by rw [List.length_append]; rw [hbytes] at hsourceCap; omega)
        (by rw [hf1.outputCount, Streaming.marks_length, hredlen]; rw [hbytes] at houtCap; omega)
      have hf := hf1.trans hf2
      refine ⟨d, (WXExec.whsT hbit e1 e2).mono ?_, hwd, ?_⟩
      · simp only [List.length_cons]
        nlinarith
      · simpa only [List.flatMap_cons, List.length_append, List.map_cons, Streaming.marks_append] using hf

end NearQuarticWires.StageModularCuts
