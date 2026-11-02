import Proof.Quartic.Control.Table

/-!
# Copying framed words out of a marked stream

Paper: Step 3 of `sec:algorithm`, paper/paper.tex, and `prop:time`: the two
stages of the reconstruction that call a subroutine (`tables`, `solved`) read a list of framed requests and write,
for each, its tag and the answer of the subroutine.

`pairP`, `pairsLoop_frame`, `unframe_exec`: a framed word `frame u` stored on a marked stream is copied as `marks u`
to another stream (one `[1, b]` per bit `b`), the head of the marked stream moving past the frame.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearQuarticWires.Reconstruct.Batch

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.RepairOrdinary.Streaming (marks marks_length marks_append)
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat (appendO appendO_st appendO_sh appendO_val appendO_cell
  appendO_append appendO_setv emitPair emitPair_spec)
open NearQuarticWires.Control
open NearCubicWires.WireExponent3_5.PrimT.ReadEq (SimW RdEq)

variable {ns nr : ℕ} (cap : ℕ) {t : ℕ}

/-- At each bit `b` of a framed word: `[1, b]` on `T`. -/
def pairP (W T : Fin (ns + 1)) (OPT : Fin nr) : WM ns nr := .ifs W (emitPair T OPT true) (emitPair T OPT false)

theorem pairP_exec (W T : Fin (ns + 1)) (OPT : Fin nr) (σ : WState ns nr) (b : Bool) (hb : wbit σ W = b)
    (hT : σ.sh T = (σ.st T).length) (hc : σ.val OPT + 2 ≤ cap) :
    WExec cap (pairP W T OPT) σ (appendO σ T OPT [true, b]) 16 := by
  cases b
  · exact WExec.ifsF hb (emitPair_spec cap T OPT false σ hT hc)
  · exact WExec.ifsT hb (emitPair_spec cap T OPT true σ hT hc)

theorem marks_cons' (b : Bool) (u : List Bool) : marks (b :: u) = [true, b] ++ marks u := by simp [marks]

/-- The scan copying the bits of a framed word as marks. -/
theorem pairsLoop_frame (W T : Fin (ns + 1)) (hWT : W ≠ T) (OPT : Fin nr) :
    ∀ (u pre rest : List Bool) (σ : WState ns nr), σ.st W = pre ++ marks (frame u) ++ rest →
      σ.sh T = (σ.st T).length → σ.val OPT + 2 * u.length ≤ cap →
      WExec cap (.whs W (scanBody W (pairP W T OPT))) (σ.seth W (pre.length + 1))
        ((appendO σ T OPT (marks u)).seth W (pre.length + 1 + 4 * u.length)) (26 * u.length + 1)
  | [], pre, rest, σ, hst, _, _ => by
    refine WExec.cast cap (WExec.whsF (frameScan_end W pre rest σ hst)) ?_ (by simp)
    simp only [List.length_nil, Nat.mul_zero, Nat.add_zero]
    rw [show marks ([] : List Bool) = [] by simp [marks],
      NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO_nil]
  | b :: u, pre, rest, σ, hst, hT, hc => by
    have e1 := fwd_at cap W σ (pre.length + 1)
    have e2 := fwd_at cap W σ (pre.length + 1 + 1)
    have e3 := pairP_exec cap W T OPT (σ.seth W (pre.length + 1 + 1 + 1)) b
      (by have := frameScan_at W b u pre rest σ hst; simpa using this)
      (by simp [Function.update_of_ne hWT.symm, hT]) (by simp; simp at hc; omega)
    set σ1 := appendO σ T OPT [true, b] with hσ1
    rw [← appendO_seth_comm _ _ _ hWT] at e3
    have e4 := fwd_at cap W σ1 (pre.length + 1 + 1 + 1)
    have e5 := fwd_at cap W σ1 (pre.length + 1 + 1 + 1 + 1)
    have h1W : σ1.st W = (pre ++ [true, true, true, b]) ++ marks (frame u) ++ rest := by
      simp [hσ1, Function.update_of_ne hWT, frameScan_tail W b u pre rest σ hst]
    have e6 := pairsLoop_frame W T hWT OPT u (pre ++ [true, true, true, b]) rest σ1 h1W
      (by simp [hσ1, hT]) (by simp [hσ1]; simp at hc; omega)
    have hlen : (pre ++ [true, true, true, b]).length + 1 = pre.length + 1 + 1 + 1 + 1 + 1 := by
      simp only [List.length_append, List.length_cons, List.length_nil]
    rw [hlen] at e6
    have hpos : pre.length + 1 + 1 + 1 + 1 + 1 + 4 * u.length = pre.length + 1 + 4 * (b :: u).length := by
      simp only [List.length_cons]; ring
    refine WExec.cast cap (WExec.whsT (frameScan_bit W b u pre rest σ hst)
      (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5)))) e6) ?_
      (by simp only [List.length_cons]; omega)
    rw [hpos, hσ1, appendO_append, marks_cons']

/-- **A framed word on a marked stream, copied as marks.** -/
theorem unframe_exec (W T : Fin (ns + 1)) (hWT : W ≠ T) (OPT : Fin nr) (u pre rest : List Bool)
    (σ : WState ns nr) (hst : σ.st W = pre ++ marks (frame u) ++ rest) (hsh : σ.sh W = pre.length)
    (hT : σ.sh T = (σ.st T).length) (hc : σ.val OPT + 2 * u.length ≤ cap) :
    WExec cap (frameScan W (pairP W T OPT)) σ
      ((appendO σ T OPT (marks u)).seth W (pre.length + (marks (frame u)).length)) (26 * u.length + 5) :=
  frameScan_exec cap W _ u pre σ _ _ hsh (pairsLoop_frame cap W T hWT OPT u pre rest σ hst hT hc)


/-! ## One item -/

/-- Append `u` to the stream `T` (head at its end), registers unchanged. -/
def appendT {ns nr : ℕ} (σ : WState ns nr) (T : Fin (ns + 1)) (u : List Bool) : WState ns nr :=
  (σ.sets T (σ.st T ++ u)).seth T (σ.sh T + u.length)

/-- The input counter of the call site. -/
def rX : Fin lnr := cY 0

/-- **One item** of the batch: its tag to the accumulator `T`, its framed input to the input tape of the call
site, the call, the answer to `T` by the copier `cp`, the cleanup. -/
noncomputable def itemP (p : Program) (cp : WM (cns p.tapeCount) lnr) : WMX (cns p.tapeCount) lnr :=
  .seq (.wm (frameScan (cIN _) (pairP (cIN _) (cT _) rT)))
  (.seq (.wm (frameScan (cIN _) (pairP (cIN _) (siteC p).input rX)))
  (.seq (.wm (emitC (siteC p).input rX false))
  (.seq (.wm (NearCubicGates.Close.Codec.rewindLoop (siteC p).input rX))
  (.seq (callP (siteC p))
  (.seq (.wm cp)
  (cleanP (siteC p)))))))

/-- The state before an item. -/
structure BatchReady (t : ℕ) (ρ : WState (cns t) lnr) : Prop where
  b : ∀ j, ρ.st (cbank t j) = []
  bh : ∀ j, ρ.sh (cbank t j) = 0
  ta : ρ.st (cTA t) = []
  tah : ρ.sh (cTA t) = 0
  ga : ρ.st (cGA t) = []
  gah : ρ.sh (cGA t) = 0
  ruler : ρ.st (cL t) = []
  rulerh : ρ.sh (cL t) = 0
  tt : ρ.sh (cT t) = (ρ.st (cT t)).length
  rs : ∀ i, ρ.val (rS i) = 0
  r : ∀ i, ρ.val (cR i) = 0
  x : ρ.val rX = 0

/-- The cost of one item. -/
def itemCost (tg w B c : ℕ) : ℕ :=
  26 * tg + 5 + 1 + (26 * w + 5 + 1 + (7 + 1 + (5 * (2 * w + 1) + 1 + 1 + (callCost w B + 1 + (c + 1 +
    cleanCost (2 * w + 2 + B))))))

/-- Two streams of the layout differ (by their indices). -/
local macro "bdst" : tactic =>
  `(tactic| (apply cne; simp [Site.input, siteC, cbank, NearCubicGates.Close.WorkerArith.inTape, cIN, cOUT, cHS,
    cCT, cT, cL, cTA, cGA] <;> omega))

/-- Two registers of the layout differ (by their indices). -/
local macro "brdst" : tactic =>
  `(tactic| (intro hh; have hv := congrArg Fin.val hh; simp [cY, cR, cZ, cOP, cC, cLC, cD, rS, rT, rX, rO, rI,
    rH] at hv <;> omega))

theorem itemP_exec {R : Type} {inp out : R → List Bool} {bud : R → ℕ} (f : WordFunction R inp out bud)
    (cp : WM (cns f.program.tapeCount) lnr) (r : R) (cpc : ℕ)
    (hcp : ∀ σ : WState (cns f.program.tapeCount) lnr, σ.st (cbank _ f.program.outputTape) = out r →
      σ.sh (cbank _ f.program.outputTape) = 0 → σ.sh (cT _) = (σ.st (cT _)).length → (∀ i, σ.val (cR i) = 0) →
      WExec cap cp σ (appendT σ (cT _) (marks (out r))) cpc)
    (ρ : WState (cns f.program.tapeCount) lnr) (hρ : BatchReady _ ρ) (tag preIN restIN : List Bool)
    (hIN : ρ.st (cIN _) = preIN ++ marks (frame tag ++ frame (inp r)) ++ restIN) (hsh : ρ.sh (cIN _) = preIN.length)
    (B : ℕ) (hB : bud r ≤ B) (hcap : ρ.val rT + 2 * tag.length + 4 * (inp r).length + B + 10 ≤ cap) :
    ∃ τ, WXExec cap (itemP f.program cp) ρ τ (itemCost tag.length (inp r).length B cpc) ∧
      SimW (appendT (appendO (ρ.seth (cIN _) (preIN.length + (marks (frame tag ++ frame (inp r))).length)) (cT _) rT
        (marks tag)) (cT _) (marks (out r))) τ := by
  have ht2 := f.program.twoTapes
  have hIT : cIN f.program.tapeCount ≠ cT _ := by bdst
  have hIX : cIN f.program.tapeCount ≠ (siteC f.program).input := by bdst
  have hTX : cT f.program.tapeCount ≠ (siteC f.program).input := by bdst
  have hmf : marks (frame tag ++ frame (inp r)) = marks (frame tag) ++ marks (frame (inp r)) := marks_append _ _
  have hfl := marks_frame_length (inp r)
  -- 1. the tag
  have e1 := unframe_exec cap (cIN _) (cT _) hIT rT tag preIN (marks (frame (inp r)) ++ restIN) ρ
    (by rw [hIN, hmf]; simp only [List.append_assoc]) hsh hρ.tt (by omega)
  set σ1 := (appendO ρ (cT _) rT (marks tag)).seth (cIN _) (preIN.length + (marks (frame tag)).length) with hσ1
  -- 2. the input onto the input tape of the site
  have hX1 : σ1.st (siteC f.program).input = [] := by
    simp [hσ1, Function.update_of_ne hTX.symm]; exact hρ.b _
  have hX1h : σ1.sh (siteC f.program).input = 0 := by
    simp [hσ1, Function.update_of_ne hTX.symm, Function.update_of_ne hIX.symm]; exact hρ.bh _
  have e2 := unframe_exec cap (cIN _) (siteC f.program).input hIX rX (inp r) (preIN ++ marks (frame tag)) restIN σ1
    (by simp only [hσ1, WState.seth_st, appendO_st, Function.update_of_ne hIT, hIN, hmf, List.append_assoc])
    (by simp [hσ1]) (by rw [hX1, hX1h]; rfl)
    (by simp [hσ1, Function.update_of_ne (show rX ≠ rT by brdst), hρ.x]; omega)
  set σ2 := (appendO σ1 (siteC f.program).input rX (marks (inp r))).seth (cIN _)
    ((preIN ++ marks (frame tag)).length + (marks (frame (inp r))).length) with hσ2
  have h2X : σ2.st (siteC f.program).input = marks (inp r) := by simp [hσ2, hX1]
  have h2Xh : σ2.sh (siteC f.program).input = (marks (inp r)).length := by
    simp [hσ2, Function.update_of_ne hIX.symm, hX1h]
  have h2v : σ2.val rX = (marks (inp r)).length := by
    simp [hσ2, hσ1, Function.update_of_ne (show rX ≠ rT by brdst), hρ.x]
  -- 3. the end of the frame
  have e3 := emitC_app cap (siteC f.program).input rX false σ2 (by rw [h2X, h2Xh]) (by rw [h2v, marks_length]; omega)
  set σ3 := appendO σ2 (siteC f.program).input rX [false] with hσ3
  -- 4. back to the start of the input tape
  have e4 := NearCubicGates.Close.Codec.rewindLoop_spec cap (siteC f.program).input rX ((marks (inp r)).length + 1) σ3
    (by simp [hσ3, h2v]) (by simp [hσ3, h2Xh]) (by rw [marks_length]; omega)
  have h3sh : σ3.sh (siteC f.program).input - ((marks (inp r)).length + 1) = 0 := by simp [hσ3, h2Xh]
  rw [h3sh] at e4
  set σ4 := (σ3.setv rX 0).seth (siteC f.program).input 0 with hσ4
  -- the streams of the site and the other streams
  have s4st : ∀ q, q ≠ (siteC f.program).input → q ≠ cT f.program.tapeCount → σ4.st q = ρ.st q := fun q h1 h2 => by
    simp [hσ4, hσ3, hσ2, hσ1, Function.update_of_ne h1, Function.update_of_ne h2]
  have s4sh : ∀ q, q ≠ (siteC f.program).input → q ≠ cT f.program.tapeCount → q ≠ cIN _ → σ4.sh q = ρ.sh q :=
    fun q h1 h2 h3 => by
      simp [hσ4, hσ3, hσ2, hσ1, Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3]
  have h4X : σ4.st (siteC f.program).input = frame (inp r) := by
    simp [hσ4, hσ3, h2X, NearCubicGates.Close.Codec.frame_eq_marks]
  have s4val : σ4.val = (appendO ρ (cT _) rT (marks tag)).val := by
    funext q
    by_cases hq : q = rX
    · subst hq; simp [hσ4, Function.update_of_ne (show rX ≠ rT by brdst), hρ.x]
    · simp [hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hq]
  -- 5. the call
  have hin5 : ∀ j, σ4.st ((siteC f.program).bank j) = f.program.inputTapes (inp r) j := by
    intro j
    by_cases hj : j = NearCubicGates.Close.WorkerArith.inTape f.program
    · subst hj
      rw [show (siteC f.program).bank (NearCubicGates.Close.WorkerArith.inTape f.program) = (siteC f.program).input
        from rfl, h4X]
      simp [Program.inputTapes, NearCubicGates.Close.WorkerArith.inTape]
    · have hne : (siteC f.program).bank j ≠ (siteC f.program).input :=
        fun h => hj ((siteC f.program).bank_inj h)
      rw [s4st _ hne (by bdst)]
      have hv : ¬ (j.val = 0) := fun h => hj (Fin.ext h)
      simp only [siteC, hρ.b, Program.inputTapes]
      rw [if_neg hv]
  obtain ⟨tA, sA, τ5, houtA, hsA, hlenA, farA, e5, sim5⟩ := callP_exec f r cap (siteC f.program) σ4 hin5
    (fun j => by
      by_cases hj : j = NearCubicGates.Close.WorkerArith.inTape f.program
      · subst hj; show σ4.sh (siteC f.program).input = 0; simp [hσ4]
      · have hne : (siteC f.program).bank j ≠ (siteC f.program).input :=
          fun h => hj ((siteC f.program).bank_inj h)
        rw [s4sh _ hne (by bdst) (by bdst)]; exact hρ.bh j)
    (by rw [s4st _ (by bdst) (by bdst)]; exact hρ.ta)
    (by rw [s4sh _ (by bdst) (by bdst) (by bdst)]; exact hρ.tah)
    (by rw [s4st _ (by bdst) (by bdst)]; exact hρ.ga)
    (by rw [s4sh _ (by bdst) (by bdst) (by bdst)]; exact hρ.gah)
    (by rw [s4st _ (by bdst) (by bdst)]; simp only [siteC, hρ.ruler]; exact blank_nil')
    (by rw [s4sh _ (by bdst) (by bdst) (by bdst)]; exact hρ.rulerh)
    (fun i => by
      show σ4.val (rS i) = 0
      rw [s4val]; simp [Function.update_of_ne (show rS i ≠ rT by brdst), hρ.rs i])
    (by omega)
  set ι5 := calledState (siteC f.program) σ4 tA (inp r).length sA with hι5
  have i5out : ∀ q, (siteC f.program).Out q → ι5.st q = σ4.st q ∧ ι5.sh q = σ4.sh q :=
    fun q hq => calledState_out _ _ _ _ _ q hq
  have oT : (siteC f.program).Out (cT f.program.tapeCount) := outC _ _ (by simp [cT])
  -- 6. the answer onto the accumulator
  have e6 := hcp ι5 (by rw [← houtA]; exact (calledState_bank (siteC f.program) σ4 tA _ _ _).1)
    (calledState_bank (siteC f.program) σ4 tA _ _ _).2
    (by
      rw [(i5out _ oT).1, (i5out _ oT).2]
      simp [hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hTX, Function.update_of_ne hIT.symm, hρ.tt])
    (fun i => by
      show σ4.val (cR i) = 0
      rw [s4val]; simp [Function.update_of_ne (show cR i ≠ rT by brdst), hρ.r i])
  set σ6 := appendT ι5 (cT _) (marks (out r)) with hσ6
  have s6st : ∀ q, q ≠ cT f.program.tapeCount → σ6.st q = ι5.st q := fun q h => by
    simp [hσ6, appendT, Function.update_of_ne h]
  have s6sh : ∀ q, q ≠ cT f.program.tapeCount → σ6.sh q = ι5.sh q := fun q h => by
    simp [hσ6, appendT, Function.update_of_ne h]
  -- 7. the cleanup
  have hbt : ∀ j, (siteC f.program).bank j ≠ cT f.program.tapeCount := fun j => by bdst
  obtain ⟨τ7, e7, sim7⟩ := cleanP_exec cap (siteC f.program) (guardLength (inp r).length sA) σ6
    (fun j q hq => by rw [s6st _ (hbt j), (calledState_bank (siteC f.program) σ4 tA _ _ _).1]; exact farA j q hq)
    (fun j => by rw [s6sh _ (hbt j)]; exact (calledState_bank (siteC f.program) σ4 tA _ _ _).2)
    (fun q hq => by
      rw [s6st _ (by bdst)]
      show readTapeBit ((calledState (siteC f.program) σ4 tA (inp r).length sA).st (siteC f.program).tally) q = false
      rw [(calledState_tally (siteC f.program) σ4 tA _ _).1]
      exact NearCubicGates.Close.CheckedPCPP.readTapeBit_beyond _ _ (by simp [guardLength] at hq ⊢; omega))
    (by
      rw [s6sh _ (by bdst)]
      show (calledState (siteC f.program) σ4 tA (inp r).length sA).sh (siteC f.program).tally = 0
      rw [(calledState_tally (siteC f.program) σ4 tA _ _).2]
      show σ4.sh (cTA _) = 0
      rw [s4sh _ (by bdst) (by bdst) (by bdst)]; exact hρ.tah)
    (by
      rw [s6st _ (by bdst)]
      exact (calledState_guard (siteC f.program) σ4 tA _ _).1)
    (by
      rw [s6sh _ (by bdst)]
      show (calledState (siteC f.program) σ4 tA (inp r).length sA).sh (siteC f.program).guard = 0
      rw [(calledState_guard (siteC f.program) σ4 tA _ _).2]
      show σ4.sh (cGA _) = 0
      rw [s4sh _ (by bdst) (by bdst) (by bdst)]; exact hρ.gah)
    (by
      rw [s6st _ (by bdst)]
      show NearCubicGates.Close.Worker.Blank (ι5.st (cL _))
      rw [(i5out _ (outC _ _ (by simp [cL]))).1, s4st _ (by bdst) (by bdst), hρ.ruler]
      exact blank_nil')
    (by
      rw [s6sh _ (by bdst)]
      show ι5.sh (cL _) = 0
      rw [(i5out _ (outC _ _ (by simp [cL]))).2, s4sh _ (by bdst) (by bdst) (by bdst)]; exact hρ.rulerh)
    (by
      show σ6.val (rS 0) = 0
      simp only [hσ6, appendT, WState.seth_val, WState.sets_val]
      show σ4.val (rS 0) = 0
      rw [s4val]; simp [Function.update_of_ne (show rS 0 ≠ rT by brdst), hρ.rs 0])
    (by unfold guardLength; omega)
  obtain ⟨τ, eτ, simτ⟩ := NearCubicGates.Close.Worker.seq_sim (WXExec.wm e1) (SimW.refl _)
    (NearCubicGates.Close.Worker.seq_sim (WXExec.wm e2) (SimW.refl _)
      (NearCubicGates.Close.Worker.seq_sim (WXExec.wm e3) (SimW.refl _)
        (NearCubicGates.Close.Worker.seq_sim (WXExec.wm e4) (SimW.refl _)
          (NearCubicGates.Close.Worker.seq_sim e5 sim5
            (NearCubicGates.Close.Worker.seq_sim (WXExec.wm e6) (SimW.refl _) ⟨_, e7, sim7⟩)))))
  refine ⟨τ, eτ.mono ?_, NearCubicGates.Close.CheckedPCPP.SimW.trans ?_ simτ⟩
  · unfold itemCost callCost cleanCost guardLength
    rw [marks_length]
    nlinarith
  · -- the end state is the state before the next item
    set ι7 := cleanState (siteC f.program) σ6 with hι7
    have i7out : ∀ q, (siteC f.program).Out q → ι7.st q = σ6.st q ∧ ι7.sh q = σ6.sh q :=
      fun q hq => cleanState_out _ _ q hq
    have hplain : ∀ q : Fin (cns f.program.tapeCount + 1), q.val < 8 → q ≠ cTA _ → q ≠ cGA _ →
        (siteC f.program).Out q := fun q h8 h6 h7 => outC _ _ (by
          have a6 : q.val ≠ 6 := fun e => h6 (Fin.ext (by simp [cTA, e]))
          have a7 : q.val ≠ 7 := fun e => h7 (Fin.ext (by simp [cGA, e]))
          omega)
    have chain : ∀ q : Fin (cns f.program.tapeCount + 1), (siteC f.program).Out q →
        ι7.st q = σ6.st q ∧ ι7.sh q = σ6.sh q ∧ σ6.st q = (if q = cT _ then ι5.st q ++ marks (out r) else ι5.st q) ∧
        ι5.st q = σ4.st q ∧ ι5.sh q = σ4.sh q := fun q hq =>
      ⟨(i7out q hq).1, (i7out q hq).2, by
        by_cases hT : q = cT _
        · subst hT; simp [hσ6, appendT]
        · simp [hT, s6st _ hT], (i5out q hq).1, (i5out q hq).2⟩
    have hval : ι7.val = σ4.val := rfl
    have hXne : ∀ q, (siteC f.program).Out q → q ≠ (siteC f.program).input := fun q hq e => hq.1 _ e.symm
    suffices heq : ι7 = appendT (appendO (ρ.seth (cIN _) (preIN.length + (marks (frame tag ++ frame (inp r))).length))
        (cT _) rT (marks tag)) (cT _) (marks (out r)) by
      rw [← heq]; exact SimW.refl _
    refine WState.eq ?_ ?_ ?_ rfl
    · funext q
      rcases streamC_cases _ q with h8 | ⟨j, rfl⟩
      · by_cases h6 : q = cTA _
        · subst h6
          rw [show ι7.sh (cTA _) = σ6.sh (siteC f.program).tally from (cleanState_tally (siteC f.program) σ6).2,
            s6sh _ (by bdst)]
          show (calledState (siteC f.program) σ4 tA (inp r).length sA).sh (siteC f.program).tally = _
          rw [(calledState_tally (siteC f.program) σ4 tA _ _).2]
          show σ4.sh (cTA _) = _
          rw [s4sh _ (by bdst) (by bdst) (by bdst)]
          simp [appendT, Function.update_of_ne (show cTA f.program.tapeCount ≠ cT _ by bdst),
            Function.update_of_ne (show cTA f.program.tapeCount ≠ cIN _ by bdst)]
        · by_cases h7 : q = cGA _
          · subst h7
            rw [show ι7.sh (cGA _) = σ6.sh (siteC f.program).guard from (cleanState_guard (siteC f.program) σ6).2,
              s6sh _ (by bdst)]
            show (calledState (siteC f.program) σ4 tA (inp r).length sA).sh (siteC f.program).guard = _
            rw [(calledState_guard (siteC f.program) σ4 tA _ _).2]
            show σ4.sh (cGA _) = _
            rw [s4sh _ (by bdst) (by bdst) (by bdst)]
            simp [appendT, Function.update_of_ne (show cGA f.program.tapeCount ≠ cT _ by bdst),
              Function.update_of_ne (show cGA f.program.tapeCount ≠ cIN _ by bdst)]
          · have hO := hplain q h8 h6 h7
            obtain ⟨-, c2, -, -, c5⟩ := chain q hO
            rw [c2]
            by_cases hT : q = cT _
            · subst hT
              have h6T : σ6.sh (cT _) = ι5.sh (cT _) + (marks (out r)).length := by simp [hσ6, appendT]
              rw [h6T, c5]
              simp [appendT, hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hTX, Function.update_of_ne hIT.symm]
            · rw [s6sh _ hT, c5]
              by_cases hI : q = cIN _
              · subst hI
                simp [hσ4, hσ3, hσ2, hσ1, appendT, Function.update_of_ne hIX, Function.update_of_ne hIT, hmf]
                omega
              · rw [s4sh _ (hXne q hO) hT hI]
                simp [appendT, Function.update_of_ne hT, Function.update_of_ne hI]
      · show (cleanState (siteC f.program) σ6).sh ((siteC f.program).bank j) = _
        rw [(cleanState_bank (siteC f.program) σ6 j).2]
        simp [appendT, Function.update_of_ne (show cbank f.program.tapeCount j ≠ cT _ by bdst),
          Function.update_of_ne (show cbank f.program.tapeCount j ≠ cIN _ by bdst), hρ.bh j]
    · funext q
      rcases streamC_cases _ q with h8 | ⟨j, rfl⟩
      · by_cases h6 : q = cTA _
        · subst h6
          rw [show ι7.st (cTA _) = [] from (cleanState_tally (siteC f.program) σ6).1]
          simp [appendT, Function.update_of_ne (show cTA f.program.tapeCount ≠ cT _ by bdst), hρ.ta]
        · by_cases h7 : q = cGA _
          · subst h7
            rw [show ι7.st (cGA _) = [] from (cleanState_guard (siteC f.program) σ6).1]
            simp [appendT, Function.update_of_ne (show cGA f.program.tapeCount ≠ cT _ by bdst), hρ.ga]
          · have hO := hplain q h8 h6 h7
            obtain ⟨c1, -, c3, c4, -⟩ := chain q hO
            rw [c1, c3, c4]
            by_cases hT : q = cT _
            · subst hT
              simp [appendT, hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hTX, List.append_assoc]
            · rw [if_neg hT, s4st _ (hXne q hO) hT]
              simp [appendT, Function.update_of_ne hT]
      · show (cleanState (siteC f.program) σ6).st ((siteC f.program).bank j) = _
        rw [(cleanState_bank (siteC f.program) σ6 j).1]
        simp [appendT, Function.update_of_ne (show cbank f.program.tapeCount j ≠ cT _ by bdst), hρ.b j]
    · rw [hval, s4val]
      simp [appendT]


/-! ## All the items -/

/-- The words of the items on the input. -/
def itemsIn {R : Type} (tag inp : R → List Bool) (items : List R) : List Bool :=
  items.flatMap fun r => frame (tag r) ++ frame (inp r)

/-- The words of the items appended to the accumulator. -/
def itemsOut {R : Type} (tag out : R → List Bool) (items : List R) : List Bool :=
  items.flatMap fun r => marks (tag r) ++ marks (out r)

/-- The marks of the tags. -/
def tagsLen {R : Type} (tag : R → List Bool) (items : List R) : ℕ := (items.flatMap fun r => marks (tag r)).length

/-- The state after the items: the accumulator extended, the tag counter advanced, the input head at `P`. -/
def loopSt (ρ : WState (cns t) lnr) (P : ℕ) (U : List Bool) (v : ℕ) : WState (cns t) lnr :=
  ((appendT ρ (cT t) U).setv rT (ρ.val rT + v)).seth (cIN t) P

/-- The cost of the items. -/
def itemsCost {R : Type} (tag inp : R → List Bool) (B : ℕ) (cpc : R → ℕ) (items : List R) : ℕ :=
  (items.map fun r => itemCost (tag r).length (inp r).length B (cpc r) + 2).sum + 1

theorem batchReady_next (ρ : WState (cns t) lnr) (hρ : BatchReady t ρ) (P : ℕ) (u v : List Bool) :
    BatchReady t (appendT (appendO (ρ.seth (cIN t) P) (cT t) rT u) (cT t) v) where
  b j := by simp [appendT, Function.update_of_ne (show cbank t j ≠ cT t by bdst), hρ.b j]
  bh j := by simp [appendT, Function.update_of_ne (show cbank t j ≠ cT t by bdst),
    Function.update_of_ne (show cbank t j ≠ cIN t by bdst), hρ.bh j]
  ta := by simp [appendT, Function.update_of_ne (show cTA t ≠ cT t by bdst), hρ.ta]
  tah := by simp [appendT, Function.update_of_ne (show cTA t ≠ cT t by bdst),
    Function.update_of_ne (show cTA t ≠ cIN t by bdst), hρ.tah]
  ga := by simp [appendT, Function.update_of_ne (show cGA t ≠ cT t by bdst), hρ.ga]
  gah := by simp [appendT, Function.update_of_ne (show cGA t ≠ cT t by bdst),
    Function.update_of_ne (show cGA t ≠ cIN t by bdst), hρ.gah]
  ruler := by simp [appendT, Function.update_of_ne (show cL t ≠ cT t by bdst), hρ.ruler]
  rulerh := by simp [appendT, Function.update_of_ne (show cL t ≠ cT t by bdst),
    Function.update_of_ne (show cL t ≠ cIN t by bdst), hρ.rulerh]
  tt := by simp [appendT, Function.update_of_ne (show cT t ≠ cIN t by bdst), hρ.tt]; ring
  rs i := by simp [appendT, Function.update_of_ne (show rS i ≠ rT by brdst), hρ.rs i]
  r i := by simp [appendT, Function.update_of_ne (show cR i ≠ rT by brdst), hρ.r i]
  x := by simp [appendT, Function.update_of_ne (show rX ≠ rT by brdst), hρ.x]

theorem itemsLoop_exec {R : Type} {inp out : R → List Bool} {bud : R → ℕ} (f : WordFunction R inp out bud)
    (cp : WM (cns f.program.tapeCount) lnr) (tag : R → List Bool) (cpc : R → ℕ) (B : ℕ) :
    ∀ (items : List R) (preIN : List Bool) (ρ : WState (cns f.program.tapeCount) lnr), BatchReady _ ρ →
      ρ.st (cIN _) = preIN ++ marks (itemsIn tag inp items) ++ [false] → ρ.sh (cIN _) = preIN.length →
      (∀ r ∈ items, bud r ≤ B) →
      (∀ r ∈ items, ∀ σ : WState (cns f.program.tapeCount) lnr, σ.st (cbank _ f.program.outputTape) = out r →
        σ.sh (cbank _ f.program.outputTape) = 0 → σ.sh (cT _) = (σ.st (cT _)).length → (∀ i, σ.val (cR i) = 0) →
        WExec cap cp σ (appendT σ (cT _) (marks (out r))) (cpc r)) →
      (∀ r ∈ items, ρ.val rT + tagsLen tag items + 2 * (tag r).length + 4 * (inp r).length + B + 10 ≤ cap) →
      ∃ τ, WXExec cap (.whs (cIN _) (itemP f.program cp)) ρ τ (itemsCost tag inp B cpc items) ∧
        SimW (loopSt ρ (preIN.length + (marks (itemsIn tag inp items)).length) (itemsOut tag out items)
          (tagsLen tag items)) τ
  | [], preIN, ρ, hρ, hIN, hsh, _, _, _ => by
    refine ⟨ρ, WXExec.whsF ?_, ?_⟩
    · simp only [wbit, hIN, hsh, itemsIn, List.flatMap_nil]
      rw [show marks ([] : List Bool) = [] by simp [marks], List.append_nil]
      have := rtb_pre preIN [false] 0; rw [Nat.add_zero] at this; rw [this]; rfl
    · have : loopSt ρ (preIN.length + (marks (itemsIn tag inp [])).length) (itemsOut tag out []) (tagsLen tag []) = ρ := by
        refine WState.eq ?_ ?_ ?_ rfl
        · funext q; by_cases hq : q = cIN _
          · subst hq; simp [loopSt, appendT, itemsIn, marks, hsh]
          · by_cases hT : q = cT _
            · subst hT; simp [loopSt, appendT, itemsOut, Function.update_of_ne hq]
            · simp [loopSt, appendT, Function.update_of_ne hq, Function.update_of_ne hT]
        · funext q; by_cases hT : q = cT _
          · subst hT; simp [loopSt, appendT, itemsOut]
          · simp [loopSt, appendT, Function.update_of_ne hT]
        · funext q; by_cases hq : q = rT
          · subst hq; simp [loopSt, appendT, tagsLen]
          · simp [loopSt, appendT, Function.update_of_ne hq]
      rw [this]; exact SimW.refl _
  | r :: items, preIN, ρ, hρ, hIN, hsh, hB, hcp, hcap => by
    have hmi : marks (itemsIn tag inp (r :: items)) = marks (frame (tag r) ++ frame (inp r)) ++
        marks (itemsIn tag inp items) := by simp [itemsIn, marks_append]
    have hT1 : tagsLen tag (r :: items) = (marks (tag r)).length + tagsLen tag items := by
      simp [tagsLen]
    obtain ⟨τ1, e1, s1⟩ := itemP_exec cap f cp r (cpc r) (hcp r (by simp)) ρ hρ (tag r) preIN
      (marks (itemsIn tag inp items) ++ [false]) (by rw [hIN, hmi]; simp only [List.append_assoc]) hsh B
      (hB r (by simp)) (by have := hcap r (by simp); omega)
    set ρ1 := appendT (appendO (ρ.seth (cIN _) (preIN.length + (marks (frame (tag r) ++ frame (inp r))).length))
      (cT _) rT (marks (tag r))) (cT _) (marks (out r)) with hρ1
    obtain ⟨τ2, e2, s2⟩ := itemsLoop_exec f cp tag cpc B items (preIN ++ marks (frame (tag r) ++ frame (inp r))) ρ1
      (batchReady_next ρ hρ _ _ _)
      (by simp [hρ1, appendT, Function.update_of_ne (show cIN f.program.tapeCount ≠ cT _ by bdst), hIN, hmi])
      (by simp [hρ1, appendT, Function.update_of_ne (show cIN f.program.tapeCount ≠ cT _ by bdst)])
      (fun x hx => hB x (by simp [hx])) (fun x hx => hcp x (by simp [hx]))
      (fun x hx => by
        have := hcap x (by simp [hx])
        simp only [hρ1, appendT, WState.seth_val, WState.sets_val, appendO_val, Function.update_self]
        rw [marks_length] at hT1 ⊢; omega)
    obtain ⟨τ3, e3, s3⟩ := NearCubicGates.Close.CheckedPCPP.wxexec_sim e2 τ1 s1
    have hb : wbit ρ (cIN _) = true := by
      simp only [wbit, hIN, hsh, hmi, List.append_assoc]
      have := rtb_pre preIN (marks (frame (tag r) ++ frame (inp r)) ++ (marks (itemsIn tag inp items) ++ [false])) 0
      rw [Nat.add_zero] at this; rw [this]
      obtain ⟨y, ys, hy⟩ : ∃ y ys, frame (tag r) ++ frame (inp r) = y :: ys := by
        cases h : tag r with
        | nil => exact ⟨false, frame (inp r), by simp [frame]⟩
        | cons b bs => exact ⟨true, b :: frame bs ++ frame (inp r), by simp [frame]⟩
      rw [hy]
      simp [marks, readTapeBit]
    refine ⟨τ3, WXExec.mono (WXExec.whsT hb e1 e3) ?_, NearCubicGates.Close.CheckedPCPP.SimW.trans ?_ s3⟩
    · simp only [itemsCost, List.map_cons, List.sum_cons]; omega
    · have heq : loopSt ρ1 ((preIN ++ marks (frame (tag r) ++ frame (inp r))).length +
          (marks (itemsIn tag inp items)).length) (itemsOut tag out items) (tagsLen tag items) =
          loopSt ρ (preIN.length + (marks (itemsIn tag inp (r :: items))).length) (itemsOut tag out (r :: items))
            (tagsLen tag (r :: items)) := by
        refine WState.eq ?_ ?_ ?_ rfl
        · funext q; by_cases hq : q = cIN _
          · subst hq; simp [loopSt, hmi]; ring
          · by_cases hT : q = cT _
            · subst hT
              simp [loopSt, hρ1, appendT, itemsOut, Function.update_of_ne hq]; ring
            · simp [loopSt, hρ1, appendT, Function.update_of_ne hq, Function.update_of_ne hT]
        · funext q; by_cases hT : q = cT _
          · subst hT
            simp [loopSt, hρ1, appendT, itemsOut, List.append_assoc]
          · simp [loopSt, hρ1, appendT, Function.update_of_ne hT]
        · funext q; by_cases hq : q = rT
          · subst hq; simp [loopSt, hρ1, appendT, hT1]; ring
          · simp [loopSt, hρ1, appendT, Function.update_of_ne hq]
      rw [← heq]; exact s2

end NearQuarticWires.Reconstruct.Batch
