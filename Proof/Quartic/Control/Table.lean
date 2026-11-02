import Proof.Quartic.Control.Start
import Proof.Quartic.Control.SeedLoop
import Proof.Quartic.StageLift.ParameterFields

/-!
# The coefficient stage

Paper: Step 3 of `sec:algorithm`, paper/paper.tex; `cor:conditional`; `prop:time`: for each of the `N^{2m}` closed walks, one coefficient `2^S c_π(w)`; the stage writes the child input
followed by the framed coefficient table (`Greedy.gammaWord`).

This file first shows that the walks never touch the output stream (`walksP_avoids`), so that the copy of the child
input written there before the walks stays exact.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearQuarticWires.Control

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.RepairOrdinary.Streaming (marks marks_length marks_append)
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat (appendO appendO_st appendO_sh appendO_val appendO_cell)

/-! ## The walks avoid the output -/

section Avoid

variable {ns nr : ℕ}

theorem emitMarks_avoids (i o : Fin (ns + 1)) (OP : Fin nr) (h : o ≠ i) :
    ∀ bs, WM.Avoids i (NearCubicGates.Close.Codec.emitMarks o OP bs)
  | [] => trivial
  | b :: bs => ⟨by simp [WM.Avoids, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.emitPair, emitC, WM.fwdC, h],
      emitMarks_avoids i o OP h bs⟩

theorem numW_avoids (i W o : Fin (ns + 1)) (X : Fin 5 ↪ Fin nr) (OP : Fin nr) (hW : W ≠ i) (ho : o ≠ i) :
    WM.Avoids i (NearCubicGates.Close.Codec.numW W o X OP) := by
  refine ⟨?_, ?_⟩
  · simp [WM.Avoids, NearCubicGates.Close.Codec.numScan, NearCubicGates.Close.Codec.countW,
      NearCubicGates.Close.Codec.scanLoop, NearCubicGates.Close.Codec.scanBody, NearCubicGates.Close.Codec.rewindLoop,
      NearCubicGates.Close.Codec.subLoop, WM.clear, hW]
  · refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · simp [WM.Avoids, NearCubicGates.Close.Codec.onesLoop, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.emitPair,
        emitC, WM.fwdC, ho]
    · simp [WM.Avoids, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.emitPair, emitC, WM.fwdC, ho]
    · simp [WM.Avoids, NearCubicGates.Close.Codec.copyBitsLoop, NearCubicGates.Close.Codec.emitScanned,
        NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.emitPair, emitC, WM.fwdC, ho, hW]
    · simp [WM.Avoids, NearCubicGates.Close.Codec.skipLoop, hW]
    · exact emitMarks_avoids i o OP ho _
    · simp [WM.Avoids, NearCubicGates.Close.Codec.skipLoop, hW]

theorem emitSlots_avoids (i CT o : Fin (ns + 1)) (Y : Fin 5 ↪ Fin nr) (OP : Fin nr) (h1 : CT ≠ i) (h2 : o ≠ i) :
    ∀ m, WM.Avoids i (emitSlots CT o Y OP m)
  | 0 => trivial
  | m + 1 => ⟨numW_avoids i CT o Y OP h1 h2, emitSlots_avoids i CT o Y OP h1 h2 m⟩

theorem incTimes_avoids (i : Fin (ns + 1)) (F : Fin nr) : ∀ m, WMX.Avoids i (incTimes F m)
  | 0 => trivial
  | m + 1 => ⟨trivial, incTimes_avoids i F m⟩

theorem copyNat_avoids (i s o : Fin (ns + 1)) (R : Fin 8 ↪ Fin nr) (hs : s ≠ i) (ho : o ≠ i) (ε : Bool) :
    WM.Avoids i (NearCubicGates.Close.Codec.copyNat ε s o R) := by
  simp [WM.Avoids, NearCubicGates.Close.Codec.copyNat, NearCubicWires.WireExponent3_5.PrimAsm.CopyNat.copyNatM,
    NearCubicWires.WireExponent3_5.PrimAsm.CopyNat.copyUnary, NearCubicWires.WireExponent3_5.PrimAsm.CopyNat.copyBit,
    NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.preE, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.emitPair,
    emitC, WM.fwdC, hs, ho]
  cases ε <;> simp [WM.Avoids, hs]

theorem copyK_avoids (i O VI : Fin (ns + 1)) (R : Fin 8 ↪ Fin nr) (hO : O ≠ i) (hV : VI ≠ i) :
    ∀ k, WM.Avoids i (NearCubicGates.Close.WorkerArith.copyK O VI R k)
  | 0 => trivial
  | k + 1 => ⟨copyNat_avoids i O VI R hO hV false, copyK_avoids i O VI R hO hV k⟩


theorem copyLoop_avoids (i S X : Fin (ns + 1)) (OP C : Fin nr) (hS : S ≠ i) (hX : X ≠ i) (dbl : Bool) :
    WMX.Avoids i (copyLoop dbl S X OP C) := by
  simp [WMX.Avoids, WM.Avoids, copyLoop, preEmit, NearCubicGates.Close.Codec.emitScanned,
    NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.emitPair, emitC, WM.fwdC, WMX.fwd, WMX.inc, hS, hX]
  cases dbl <;> simp [WMX.Avoids, WM.Avoids, preEmit, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.emitPair, emitC,
    WM.fwdC, WMX.skip, hX]

theorem writeRequest_avoids (i HS CT X : Fin (ns + 1)) (OP C LC D : Fin nr) (Y : Fin 5 ↪ Fin nr) (m : ℕ)
    (hH : HS ≠ i) (hC : CT ≠ i) (hX : X ≠ i) : WMX.Avoids i (writeRequest m HS CT X OP C LC D Y) := by
  refine ⟨copyLoop_avoids i HS X OP C hH hX false, ?_, emitMarks_avoids i X OP hX _, emitSlots_avoids i CT X Y OP hC hX m,
    ?_, ?_, ?_, ?_⟩
  · simp [WMX.Avoids, WM.Avoids, NearCubicGates.Close.Codec.rewindLoop, hH]
  · simp [WMX.Avoids, WM.Avoids, emitC, WM.fwdC, hX]
  · simp [WMX.Avoids, WM.Avoids, WM.rewind, hX]
  · simp [WMX.Avoids, WM.Avoids, NearCubicGates.Close.Codec.dupR, WM.move]
  · simp [WMX.Avoids, WM.Avoids, NearCubicGates.Close.Codec.rewindLoop, hC]

theorem incWalk_avoids (i CT : Fin (ns + 1)) (Z : Fin 5 ↪ Fin nr) (LC C D : Fin nr) (m : ℕ) (hC : CT ≠ i) :
    WMX.Avoids i (incWalk m CT Z LC C D) := by
  refine ⟨trivial, incTimes_avoids i _ m, ?_, ?_, ?_⟩
  · simp [WMX.Avoids, WM.Avoids, fieldsLoop, fieldStep, bitsLoop, NearCubicGates.Close.Codec.dupR, WM.move,
      NearCubicGates.Close.Codec.skipLoop, WMX.fwd, WMX.dec, WMX.wr, WMX.skip, hC]
  · simp [WMX.Avoids, WM.Avoids, NearCubicGates.Close.Codec.dupR, WM.move]
  · simp [WMX.Avoids, WM.Avoids, NearCubicGates.Close.Codec.rewindLoop, hC]

/-- **The walks never touch the output stream.** -/
theorem walksP_avoids (p : Program) : WMX.Avoids (cOUT p.tapeCount) (walksP p) := by
  have hb : ∀ j, cbank p.tapeCount j ≠ cOUT _ := fun j => cne _ (by simp [cbank, cOUT]; omega)
  refine ⟨⟨writeRequest_avoids _ _ _ _ _ _ _ _ _ 8 (cne _ (by simp [cHS, cOUT])) (cne _ (by simp [cCT, cOUT]))
      (hb _), ?_, ?_, ?_, incWalk_avoids _ _ _ _ _ _ 8 (cne _ (by simp [cCT, cOUT]))⟩, ?_⟩
  · simp [WMX.Avoids, WM.Avoids, callP, WMX.machZ, NearCubicGates.Close.WorkerArith.guardP,
      NearCubicGates.Close.WorkerArith.tallyP, NearCubicGates.Close.WorkerArith.twoOnes, BinW.width, BinW.widthW,
      BinW.widthLoop, BinW.backLoop, WM.rewind, WMX.wr, WMX.fwd, WMX.inc, WMX.dec, WMX.skip, Site.input, siteC,
      cTA, cGA, cL, cOUT, cbank, Fin.ext_iff]
    all_goals (repeat' (first | apply And.intro | apply addCases_val (P := fun v => ¬ v = 1)))
    all_goals first | omega | (intro j; simp [cbank]; omega) | simp
  · exact ⟨copyK_avoids _ _ _ _ (hb _) (cne _ (by simp [cT, cOUT])) 2, by simp [WM.Avoids, halfRewind]; exact hb _⟩
  · simp [WMX.Avoids, WM.Avoids, cleanP, eraseP, WMX.machZ, Site.swept, NearCubicGates.Close.WorkerArith.clearSelfP,
      WMX.wr, WMX.fwd, WMX.bwd, WMX.inc, WMX.dec, WMX.skip, WM.rewind, siteC, cTA, cGA, cL, cOUT, cbank, Fin.ext_iff]
    all_goals (repeat' (first | apply And.intro | apply addCases_val (P := fun v => ¬ v = 1)))
    all_goals first | omega | (intro j; simp [cbank]; omega) | (intro h; cases h)
  · simp [WMX.Avoids, WM.Avoids, flagStep, WMX.dec, WMX.skip]

end Avoid


/-! ## The child input, field by field -/

/-- The parameters after `ℓ_f` are numbers, two lists and numbers (`StageLift.parametersWord_block_layout`). -/
theorem paramsTail_layout (p : Cells.Parameters) :
    natWord p.S ++ paramsTail p = ((StageLift.parameterHeadScalars p).drop 19).flatMap natWord ++
      NearCubicGates.Close.Interfaces.listWord natWord (p.primes.sort (· ≤ ·)) ++
      (StageLift.parameterTailScalars p).flatMap natWord ++ NearCubicGates.Close.Interfaces.listWord natWord p.factors := by
  have h1 := parametersWord_split p
  have h2 := StageLift.parametersWord_block_layout p
  have h3 : StageLift.parameterHeadScalars p = params19 p ++ (StageLift.parameterHeadScalars p).drop 19 := by
    simp [StageLift.parameterHeadScalars, params19]
  rw [h2, h3, List.flatMap_append] at h1
  simp only [List.append_assoc] at h1
  exact (List.append_cancel_left h1).symm.trans (by simp only [List.append_assoc])


/-- The six parameters before `k`. -/
def params6 (p : Cells.Parameters) : List ℕ := [p.lambda, p.mu, p.m, p.r, p.s, p.b]

/-- The ten parameters between `k` and `Q`. -/
def params10 (p : Cells.Parameters) : List ℕ := [p.N, p.Jmax, p.T, p.tau, p.U, p.Xmax, p.dstar, p.omega1, p.omega2, p.MF]

/-- **The child input, field by field**: the seed parameters `k`, `Q`, `ℓ_f` at their places, then the rest of the
parameters, the two frames of Step 2 and `frame π`. -/
theorem childInput_fields {B1 B2 : ℕ} (q : Greedy.ChildRequest B1 B2) :
    Greedy.childInput q = seedPre q.call (params6 q.selected.1) q.selected.1.k (params10 q.selected.1)
      q.selected.1.Q q.selected.1.ellf ++
      (tailWord ((StageLift.parameterHeadScalars q.selected.1).drop 19) (q.selected.1.primes.sort (· ≤ ·))
        (StageLift.parameterTailScalars q.selected.1) q.selected.1.factors
        (Program.witnessPrefix q.call q.selected.1 q.witness)
        (Program.certifiedBits (Program.runCall q.call q.selected q.witness)) ++ frame q.seedPrefix) := by
  unfold Greedy.childInput
  rw [certWord_of_dispatch q.dispatched]
  simp only [List.append_assoc]
  rw [← List.append_assoc (natWord (q.selected.1).S) (paramsTail _), paramsTail_layout]
  simp only [seedPre, tailWord, params19, params6, params10, List.flatMap_cons, List.flatMap_nil, List.append_assoc,
    List.append_nil]


/-! ## The last phase -/

/-- **The framed table after the child input.** If the output holds exactly `marks w` (head at its end) and the
table reads, from its head, like `marks U`, the last phase leaves exactly `frame (w ++ frame U)` on the output. -/
theorem tableTail_exec {ns : ℕ} (cap : ℕ) (σ : WState ns lnr) (T O : Fin (ns + 1)) (hTO : T ≠ O) (w U : List Bool)
    (hT : ∀ q, readTapeBit (σ.st T) (σ.sh T + q) = readTapeBit (marks U ++ []) q)
    (hO : σ.st O = marks w) (hOh : σ.sh O = 2 * w.length) (hOP : σ.val rO = 2 * w.length) (hC : σ.val rI = 0)
    (hc : 6 * w.length + 6 * U.length + 20 ≤ cap) :
    ∃ τ, WXExec cap (.seq (copyLoop true T O rO rI)
      (.seq (.wm (NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.emitPair O rO false)) (.wm (emitC O rO false)))) σ τ
        (U.length * 52 + 1 + 1 + (15 + 1 + 7)) ∧ τ.st O = frame (w ++ frame U) := by
  have hOC : rO ≠ rI := by decide
  have e2 := copyLoop_exec_read cap σ T O rO rI true hTO hOC U [] hT rfl (by rw [hO, hOh, marks_length])
    (by omega) (by omega)
  rw [bitCells_true] at e2
  set σ2 := copySt σ T O rO rI U.length (marks (marks U)) with hσ2
  have h2Oh : σ2.sh O = (σ2.st O).length := by
    simp [hσ2, copySt, Function.update_of_ne hTO.symm, hO, hOh, marks_length]
  have h2OP : σ2.val rO = 2 * w.length + 4 * U.length := by
    simp [hσ2, copySt, Function.update_of_ne hOC, hOP, marks_length]; ring
  have e3 := NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.emitPair_spec cap O rO false σ2 h2Oh (by omega)
  set σ3 := appendO σ2 O rO [true, false] with hσ3
  have e4 := emitC_spec cap O rO false σ3 (by simp [hσ3, h2Oh]) (by simp [hσ3, h2OP]; omega)
  refine ⟨_, WXExec.seq e2 (WXExec.seq (WXExec.wm e3) (WXExec.wm e4)), ?_⟩
  simp only [WState.setv_st, WState.seth_st, WState.sets_st, Function.update_self]
  rw [tableFrame_eq]
  simp [hσ3, hσ2, copySt, hO, List.append_assoc]


/-! ## The first phase -/

/-- The start of the coefficient stage (`Expand.PolyTab.idealStart`): `frame w` on the input, every other stream
empty, every head and register at `0`. -/
abbrev gammaStart (t : ℕ) (w : List Bool) : WState (cns t) lnr :=
  NearCubicGates.Close.Expand.PolyTab.idealStart (cns t) lnr w (fun _ => 0)

theorem gammaStart_st (t : ℕ) (w : List Bool) (q : Fin (cns t + 1)) :
    (gammaStart t w).st q = if q.val = 0 then frame w else [] := by
  simp [NearCubicGates.Close.Expand.PolyTab.idealStart]

/-- **The child input on the output**: copy `marks w` to the output, then bring the input head back. -/
theorem inputCopy_exec (cap t : ℕ) (w : List Bool) (hc : 6 * w.length + 6 ≤ cap) :
    WXExec cap (.seq (copyLoop false (cIN t) (cOUT t) rO rI) (.wm (NearCubicGates.Close.Codec.rewindLoop (cIN t) rI)))
      (gammaStart t w) (appendO (gammaStart t w) (cOUT t) rO (marks w)) (w.length * 52 + 1 + 1 + (5 * (2 * w.length) + 1)) := by
  have hIO : cIN t ≠ cOUT t := cne _ (by simp [cIN, cOUT])
  have hOC : rO ≠ rI := by decide
  have e1 := copyLoop_exec_read cap (gammaStart t w) (cIN t) (cOUT t) rO rI false hIO hOC w [false]
    (fun q => by rw [gammaStart_st]; simp [cIN, NearCubicGates.Close.Codec.frame_eq_marks, NearCubicGates.Close.Expand.PolyTab.idealStart]) rfl
    (by rw [gammaStart_st]; simp [cOUT, NearCubicGates.Close.Expand.PolyTab.idealStart])
    (by simp [NearCubicGates.Close.Expand.PolyTab.idealStart]; omega)
    (by simp [NearCubicGates.Close.Expand.PolyTab.idealStart]; omega)
  rw [bitCells_false] at e1
  have e2 := NearCubicGates.Close.Codec.rewindLoop_spec cap (cIN t) rI (2 * w.length)
    (copySt (gammaStart t w) (cIN t) (cOUT t) rO rI w.length (marks w))
    (by simp [copySt, NearCubicGates.Close.Expand.PolyTab.idealStart])
    (by simp [copySt, Function.update_of_ne hIO, NearCubicGates.Close.Expand.PolyTab.idealStart]) (by omega)
  refine WXExec.seq e1 (WXExec.wm (WExec.cast cap e2 ?_ le_rfl))
  refine WState.eq ?_ ?_ ?_ rfl
  · funext q; by_cases hq : q = cIN t
    · subst hq; simp [copySt, Function.update_of_ne hIO, NearCubicGates.Close.Expand.PolyTab.idealStart]
    · simp [copySt, Function.update_apply, hq, NearCubicGates.Close.Expand.PolyTab.idealStart, marks_length]
  · funext q; simp [copySt]
  · funext r; by_cases hr : r = rI
    · subst hr; simp [copySt, Function.update_of_ne hOC.symm, NearCubicGates.Close.Expand.PolyTab.idealStart]
    · simp [copySt, Function.update_of_ne hr, NearCubicGates.Close.Expand.PolyTab.idealStart, marks_length]

end NearQuarticWires.Control
