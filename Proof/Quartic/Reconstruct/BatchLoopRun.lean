import Proof.Quartic.Reconstruct.BatchLoop

/-!
# The batch of calls

Paper: Step 3 of `sec:algorithm`, paper/paper.tex, and `prop:time`: the stages
`tables` and `solved` of the reconstruction read a context `pre` and a list of framed requests `(tag, input)` and
write the context and, for each request, its tag and the answer of the called word function.

`batchP` maps `frame pre ++ listWord (frame tag ++ frame inp)` to `frame (pre ++ listWord (tag ++ out))`
(`batchP_exec`). The answers are accumulated on the table stream `T` behind two zero cells, then copied to the
output: the calls never touch the output stream (`itemP_avoids`), so the output word is exact. The calls go through
`Control.callP` and `Control.cleanP`, whose cost does not depend on the number of tapes of the called program.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearQuarticWires.Reconstruct.Batch

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.RepairOrdinary.Streaming (marks marks_length marks_append)
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat (appendO appendO_st appendO_sh appendO_val appendO_cell
  appendO_append appendO_setv emitPair emitPair_spec)
open NearQuarticWires.Control
open NearCubicWires.WireExponent3_5.PrimT.ReadEq (SimW RdEq)

/-- **Every item avoids the output stream**, if the copier does. -/
theorem itemP_avoids (p : Program) (cp : WM (cns p.tapeCount) lnr) (hcp : WM.Avoids (cOUT p.tapeCount) cp) :
    WMX.Avoids (cOUT p.tapeCount) (itemP p cp) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, hcp, ?_⟩
  · simp [WMX.Avoids, WM.Avoids, frameScan, scanBody, pairP, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.emitPair,
      emitC, WM.fwdC, cIN, cOUT, cT, Fin.ext_iff]
  · simp [WMX.Avoids, WM.Avoids, frameScan, scanBody, pairP, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.emitPair,
      emitC, WM.fwdC, cIN, cOUT, Site.input, siteC, cbank, Fin.ext_iff]; omega
  · simp [WMX.Avoids, WM.Avoids, emitC, WM.fwdC, cOUT, Site.input, siteC, cbank, Fin.ext_iff]; omega
  · simp [WMX.Avoids, WM.Avoids, NearCubicGates.Close.Codec.rewindLoop, cOUT, Site.input, siteC, cbank,
      Fin.ext_iff]; omega
  · simp [WMX.Avoids, WM.Avoids, callP, WMX.machZ, NearCubicGates.Close.WorkerArith.guardP,
      NearCubicGates.Close.WorkerArith.tallyP, NearCubicGates.Close.WorkerArith.twoOnes, BinW.width, BinW.widthW,
      BinW.widthLoop, BinW.backLoop, WM.rewind, WMX.wr, WMX.fwd, WMX.inc, WMX.dec, WMX.skip, Site.input, siteC,
      cTA, cGA, cL, cOUT, cbank, Fin.ext_iff]
    all_goals (repeat' (first | apply And.intro | apply addCases_val (P := fun v => ¬ v = 1)))
    all_goals first | omega | (intro j; simp [cbank]; omega) | simp
  · simp [WMX.Avoids, WM.Avoids, cleanP, eraseP, WMX.machZ, Site.swept, NearCubicGates.Close.WorkerArith.clearSelfP,
      WMX.wr, WMX.fwd, WMX.bwd, WMX.inc, WMX.dec, WMX.skip, WM.rewind, siteC, cTA, cGA, cL, cOUT, cbank, Fin.ext_iff]
    all_goals (repeat' (first | apply And.intro | apply addCases_val (P := fun v => ¬ v = 1)))
    all_goals first | omega | (intro j; simp [cbank]; omega) | (intro h; cases h)


/-! ## The batch -/

/-- Two streams of the layout differ (by their indices). -/
local macro "bdst2" : tactic =>
  `(tactic| (apply cne; simp [Site.input, siteC, cbank, NearCubicGates.Close.WorkerArith.inTape, cIN, cOUT, cHS,
    cCT, cT, cL, cTA, cGA] <;> omega))

/-- Two registers of the layout differ (by their indices). -/
local macro "brdst2" : tactic =>
  `(tactic| (intro hh; have hv := congrArg Fin.val hh; simp [cY, cR, cZ, cOP, cC, cLC, cD, rS, rT, rX, rO, rI,
    rH] at hv <;> omega))

@[simp] theorem gammaStart_sh' (t : ℕ) (w : List Bool) (q : Fin (cns t + 1)) : (gammaStart t w).sh q = 0 := rfl
@[simp] theorem gammaStart_val' (t : ℕ) (w : List Bool) (r : Fin lnr) : (gammaStart t w).val r = 0 := rfl

/-- **The batch program** for the called program `p` and the copier `cp` of its answers. -/
noncomputable def batchP (p : Program) (cp : WM (cns p.tapeCount) lnr) : WMX (cns p.tapeCount) lnr :=
  .seq (.wm (.seq (emitC (cT _) rT false) (.seq (emitC (cT _) rT false)
    (.seq (frameScan (cIN _) (pairP (cIN _) (cT _) rT))
      (NearCubicWires.WireExponent3_5.PrimAsm.CopyNat.copyNatM true (cIN _) (cT _) (cR 0) (cR 1) rT)))))
  (.seq (.whs (cIN _) (itemP p cp))
  (.seq (.wm (sentinelRewind (cT _)))
  (.seq (copyLoop false (cT _) (cOUT _) rO rI) (.wm (emitC (cOUT _) rO false)))))

/-- The word written by the batch, before its frame. -/
def batchOut {R : Type} (pre : List Bool) (tag out : R → List Bool) (items : List R) : List Bool :=
  pre ++ NearCubicGates.Close.Interfaces.listWord (fun r => tag r ++ out r) items

/-- The cost of the batch. -/
def batchCost {R : Type} (pre : List Bool) (tag inp out : R → List Bool) (B : ℕ) (cpc : R → ℕ) (items : List R) : ℕ :=
  7 + 1 + (7 + 1 + (26 * pre.length + 5 + 1 + (60 * (RepairRepresentation.natWord items.length).length + 60))) + 1 +
    (itemsCost tag inp B cpc items + 1 + (5 * (batchOut pre tag out items).length + 9 + 1 +
      ((batchOut pre tag out items).length * 52 + 1 + 1 + 7)))

theorem itemsIn_le {R : Type} (tag inp : R → List Bool) (items : List R) (r : R) (hr : r ∈ items) :
    (tag r).length + (inp r).length ≤ (itemsIn tag inp items).length := by
  have := length_le_flatMap (fun r => frame (tag r) ++ frame (inp r)) items r hr
  simp only [List.length_append, RepairOrdinary.frame_length] at this
  unfold itemsIn; omega

theorem tagsLen_le {R : Type} (tag inp : R → List Bool) (items : List R) :
    tagsLen tag items ≤ 2 * (itemsIn tag inp items).length := by
  unfold tagsLen itemsIn
  induction items with
  | nil => simp
  | cons r rs ih =>
    simp only [List.flatMap_cons, List.length_append, marks_length, RepairOrdinary.frame_length] at ih ⊢
    omega

theorem itemsOut_eq {R : Type} (tag out : R → List Bool) (items : List R) :
    itemsOut tag out items = marks (items.flatMap fun r => tag r ++ out r) := by
  unfold itemsOut
  rw [NearCubicGates.Close.Codec.marks_flatMap]
  simp [marks_append]

/-- **The batch of calls.** From the start on `frame pre ++ listWord (frame tag ++ frame inp)`, with a called word
function `f` of budget at most `B` on the items and a copier `cp` of its answers, the program writes exactly
`frame (pre ++ listWord (tag ++ out))` on the output. -/
theorem batchP_exec (cap : ℕ) {R : Type} {inp out : R → List Bool} {bud : R → ℕ} (f : WordFunction R inp out bud)
    (cp : WM (cns f.program.tapeCount) lnr) (hcpA : WM.Avoids (cOUT _) cp) (tag : R → List Bool) (cpc : R → ℕ)
    (B : ℕ) (pre : List Bool) (items : List R) (hB : ∀ r ∈ items, bud r ≤ B)
    (hcp : ∀ r ∈ items, ∀ σ : WState (cns f.program.tapeCount) lnr, σ.st (cbank _ f.program.outputTape) = out r →
      σ.sh (cbank _ f.program.outputTape) = 0 → σ.sh (cT _) = (σ.st (cT _)).length → (∀ i, σ.val (cR i) = 0) →
      WExec cap cp σ (appendT σ (cT _) (marks (out r))) (cpc r))
    (hcap : 10 * ((frame pre ++ NearCubicGates.Close.Interfaces.listWord (fun r => frame (tag r) ++ frame (inp r))
      items).length + (batchOut pre tag out items).length + B + 10) ≤ cap) :
    ∃ τ, WXExec cap (batchP f.program cp)
      (gammaStart _ (frame pre ++ NearCubicGates.Close.Interfaces.listWord (fun r => frame (tag r) ++ frame (inp r))
        items)) τ (batchCost pre tag inp out B cpc items) ∧
      τ.st (cOUT _) = frame (batchOut pre tag out items) := by
  set W := frame pre ++ NearCubicGates.Close.Interfaces.listWord (fun r => frame (tag r) ++ frame (inp r)) items with hW
  set U := batchOut pre tag out items with hU
  have hIT : cIN f.program.tapeCount ≠ cT f.program.tapeCount := cne _ (by simp [cIN, cT])
  have hTO : cT f.program.tapeCount ≠ cOUT f.program.tapeCount := cne _ (by simp [cT, cOUT])
  have hIO : cIN f.program.tapeCount ≠ cOUT f.program.tapeCount := cne _ (by simp [cIN, cOUT])
  have hWl : W.length = (frame pre).length + (RepairRepresentation.natWord items.length).length +
      (itemsIn tag inp items).length := by
    simp only [hW, NearCubicGates.Close.Interfaces.listWord, itemsIn, List.length_append]; omega
  have hfp := RepairOrdinary.frame_length pre
  have hmfp := marks_frame_length pre
  have hnw := NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_length items.length
  set σ0 := gammaStart f.program.tapeCount W with hσ0
  have h0IN : σ0.st (cIN f.program.tapeCount) = marks (frame pre) ++ marks (RepairRepresentation.natWord items.length) ++
      (marks (itemsIn tag inp items) ++ [false]) := by
    rw [hσ0, gammaStart_st, if_pos (by simp [cIN]), NearCubicGates.Close.Codec.frame_eq_marks W]
    simp only [hW, NearCubicGates.Close.Interfaces.listWord, itemsIn, marks_append, List.append_assoc]
  have h0T : σ0.st (cT f.program.tapeCount) = [] := by rw [hσ0, gammaStart_st]; simp [cT]
  have h0Th : σ0.sh (cT f.program.tapeCount) = 0 := rfl
  -- the start of the accumulator and the context
  have e1 := emitC_app cap (cT f.program.tapeCount) rT false σ0 (by rw [h0T, h0Th]; rfl) (by simp [hσ0]; omega)
  set σ1 := appendO σ0 (cT f.program.tapeCount) rT [false] with hσ1
  have e2 := emitC_app cap (cT f.program.tapeCount) rT false σ1 (by simp [hσ1, h0T, h0Th]) (by simp [hσ1, hσ0]; omega)
  set σ2 := appendO σ1 (cT f.program.tapeCount) rT [false] with hσ2
  have e3 := unframe_exec cap (cIN f.program.tapeCount) (cT f.program.tapeCount) hIT rT pre [] (marks (RepairRepresentation.natWord items.length) ++
    (marks (itemsIn tag inp items) ++ [false])) σ2
    (by simp [hσ2, hσ1, Function.update_of_ne hIT, h0IN, List.append_assoc])
    (by simp [hσ2, hσ1, hσ0, Function.update_of_ne hIT])
    (by simp [hσ2, hσ1, h0T, h0Th]) (by simp [hσ2, hσ1, hσ0, Function.update_apply, rT, rX, cY]; omega)
  set σ3 := (appendO σ2 (cT f.program.tapeCount) rT (marks pre)).seth (cIN f.program.tapeCount) ([].length + (marks (frame pre)).length) with hσ3
  have e4 := NearCubicWires.WireExponent3_5.PrimAsm.CopyNat.copyNatM_spec cap true (cIN f.program.tapeCount) (cT f.program.tapeCount) hIT (cR 0) (cR 1) rT
    (by decide) (by decide) (by decide) items.length (marks (frame pre)) (marks (itemsIn tag inp items) ++ [false]) σ3
    (by simp [hσ3, hσ2, hσ1, Function.update_of_ne hIT, h0IN, enc_true, List.append_assoc])
    (by simp [hσ3]) (by simp [hσ3, hσ2, hσ1, Function.update_of_ne hIT.symm, h0T, h0Th]; ring)
    (by simp [hσ3, hσ2, hσ1, hσ0, Function.update_apply, cR, rT])
    (by simp [hσ3, hσ2, hσ1, hσ0, Function.update_apply, cR, rT])
    (by simp [hσ3, hσ2, hσ1, hσ0, marks_length]; omega)
  set σ4 := (appendO σ3 (cT f.program.tapeCount) rT (marks (RepairRepresentation.natWord items.length))).seth (cIN f.program.tapeCount)
    ((marks (frame pre)).length + NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.stp true *
      (RepairRepresentation.natWord items.length).length) with hσ4
  have s4st : ∀ q, q ≠ cT f.program.tapeCount → σ4.st q = σ0.st q := fun q h => by
    simp [hσ4, hσ3, hσ2, hσ1, Function.update_of_ne h]
  have s4sh : ∀ q, q ≠ cT f.program.tapeCount → q ≠ cIN f.program.tapeCount → σ4.sh q = 0 := fun q h1 h2 => by
    simp [hσ4, hσ3, hσ2, hσ1, hσ0, Function.update_of_ne h1, Function.update_of_ne h2]
  have s4val : ∀ r, r ≠ rT → σ4.val r = 0 := fun r h => by
    simp [hσ4, hσ3, hσ2, hσ1, hσ0, Function.update_of_ne h]
  have h4T : σ4.st (cT f.program.tapeCount) = [false] ++ [false] ++ marks pre ++ marks (RepairRepresentation.natWord items.length) := by
    simp [hσ4, hσ3, hσ2, hσ1, h0T, Function.update_of_ne hIT.symm]
  have h4Th : σ4.sh (cT f.program.tapeCount) = (σ4.st (cT f.program.tapeCount)).length := by
    rw [h4T]; simp [hσ4, hσ3, hσ2, hσ1, h0T, h0Th, Function.update_of_ne hIT.symm, marks_length] <;> ring
  have h4rT : σ4.val rT = 2 + (marks pre).length + (marks (RepairRepresentation.natWord items.length)).length := by
    simp [hσ4, hσ3, hσ2, hσ1, hσ0] <;> ring
  have hready : BatchReady _ σ4 := {
    b := fun j => by
      rw [s4st _ (by bdst2), hσ0, gammaStart_st]
      simp [cbank]
    bh := fun j => s4sh _ (by bdst2) (by bdst2)
    ta := by rw [s4st _ (by bdst2), hσ0, gammaStart_st]; simp [cTA]
    tah := s4sh _ (by bdst2) (by bdst2)
    ga := by rw [s4st _ (by bdst2), hσ0, gammaStart_st]; simp [cGA]
    gah := s4sh _ (by bdst2) (by bdst2)
    ruler := by rw [s4st _ (by bdst2), hσ0, gammaStart_st]; simp [cL]
    rulerh := s4sh _ (by bdst2) (by bdst2)
    tt := h4Th
    rs := fun i => s4val _ (by brdst2)
    r := fun i => s4val _ (by brdst2)
    x := s4val _ (by brdst2) }
  have h4IN : σ4.st (cIN f.program.tapeCount) = (marks (frame pre) ++ marks (RepairRepresentation.natWord items.length)) ++
      marks (itemsIn tag inp items) ++ [false] := by
    rw [s4st _ hIT, h0IN]; simp only [List.append_assoc]
  have h4INh : σ4.sh (cIN f.program.tapeCount) = (marks (frame pre) ++ marks (RepairRepresentation.natWord items.length)).length := by
    simp [hσ4, marks_length, NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.stp]
  -- the items
  have hT := tagsLen_le tag inp items
  obtain ⟨τ5, E5, S5⟩ := itemsLoop_exec cap f cp tag cpc B items _ σ4 hready h4IN h4INh hB hcp
    (fun r hr => by
      have := itemsIn_le tag inp items r hr
      rw [h4rT]; simp only [marks_length] at *; omega)
  have hOUT5 := WXExec.avoids E5 (itemP_avoids f.program cp hcpA)
  set I5 := loopSt σ4 ((marks (frame pre) ++ marks (RepairRepresentation.natWord items.length)).length +
    (marks (itemsIn tag inp items)).length) (itemsOut tag out items) (tagsLen tag items) with hI5
  have h5T : I5.st (cT f.program.tapeCount) = [] ++ [false, false] ++ marks U := by
    simp only [hI5, loopSt, appendT, WState.seth_st, WState.setv_st, WState.sets_st, Function.update_self, h4T,
      itemsOut_eq, hU, batchOut, NearCubicGates.Close.Interfaces.listWord, marks_append, List.append_assoc]
    rfl
  have h5Th : I5.sh (cT f.program.tapeCount) = (I5.st (cT f.program.tapeCount)).length := by
    simp [hI5, loopSt, appendT, Function.update_of_ne hIT.symm, h4Th]
  -- the accumulator back to its start
  have e6 := sentinelRewind_exec cap (cT f.program.tapeCount) [] U I5 h5T h5Th
  obtain ⟨τ6, E6, S6⟩ := NearCubicGates.Close.CheckedPCPP.wxexec_sim (WXExec.wm e6) τ5 S5
  have hOUT6 := WXExec.avoids E6 (show WMX.Avoids (cOUT f.program.tapeCount) (.wm (sentinelRewind (cT f.program.tapeCount))) by
    simp [WMX.Avoids, WM.Avoids, sentinelRewind, hTO])
  have h0O : σ4.st (cOUT f.program.tapeCount) = [] := by rw [s4st _ hTO.symm, hσ0, gammaStart_st]; simp [cOUT]
  have h0Oh : σ4.sh (cOUT f.program.tapeCount) = 0 := s4sh _ hTO.symm hIO.symm
  have hval6 : ∀ r, r ≠ rT → τ6.val r = 0 := fun r h => by
    rw [S6.val]; simp [hI5, loopSt, appendT, Function.update_of_ne h, s4val r h]
  -- the output
  have hread : ∀ q, readTapeBit (τ6.st (cT f.program.tapeCount)) (τ6.sh (cT f.program.tapeCount) + q) = readTapeBit (marks U ++ []) q := by
    intro q
    rw [S6.sh, ← S6.st (cT f.program.tapeCount)]
    simp only [WState.seth_st, WState.seth_sh, Function.update_self, h5T, List.append_nil, List.nil_append,
      List.length_nil, Nat.zero_add]
    exact rtb_pre [false, false] (marks U) q
  have E7 := copyLoop_exec_read cap τ6 (cT f.program.tapeCount) (cOUT f.program.tapeCount) rO rI false hTO (by decide) U [] hread rfl
    (by rw [hOUT6.1, hOUT6.2, hOUT5.1, hOUT5.2, h0O, h0Oh]; rfl)
    (by rw [hval6 _ (by decide)]; omega) (by rw [hval6 _ (by decide)]; omega)
  rw [bitCells_false] at E7
  set σ7 := copySt τ6 (cT f.program.tapeCount) (cOUT f.program.tapeCount) rO rI U.length (marks U) with hσ7
  have h7O : σ7.st (cOUT f.program.tapeCount) = marks U := by
    simp [hσ7, copySt, hOUT6.1, hOUT5.1, h0O]
  have E8 := emitC_spec cap (cOUT f.program.tapeCount) rO false σ7
    (by rw [h7O]; simp [hσ7, copySt, Function.update_of_ne hTO.symm, hOUT6.2, hOUT5.2, h0Oh, marks_length])
    (by simp [hσ7, copySt, Function.update_of_ne (show rO ≠ rI by decide), hval6 rO (by decide), marks_length]; omega)
  refine ⟨_, WXExec.mono (WXExec.seq (WXExec.wm (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4))))
    (WXExec.seq E5 (WXExec.seq E6 (WXExec.seq E7 (WXExec.wm E8))))) ?_, ?_⟩
  · unfold batchCost; simp only [hU] at *; omega
  · simp only [WState.setv_st, WState.seth_st, WState.sets_st, Function.update_self, h7O]
    rw [NearCubicGates.Close.Codec.frame_eq_marks]

end NearQuarticWires.Reconstruct.Batch
