import Proof.Quartic.Control.Erase
import Proof.Gates.WorkerArith.CtrCall

/-!
# A repeatable call of a word function

Paper: `prop:time`, paper/paper.tex: Step 3 makes `2S` child evaluations, each child
computes `N^{2m}` coefficients and prints and solves its tables, and the running time of each step
is the number of calls times the cost of one call, plus a polynomial overhead.

A *call site* (`Site`) of a word function `f` inside a word program is a bank of streams for the tapes of `f`, a
tally stream, a guard stream, a ruler and four registers. One call is two phases:

* `callP` (`callP_exec`): from the input tapes of `f` on the bank, write the guard `G = 1^{2|x|+2}` (`x` the input
  word), run the program of `f` with a clock that leaves the tally `1^s` of its `s` steps, and append the tally to the
  guard, so that `G = 1^g` with `g = 2|x| + 2 + s`. The output tape of `f` then holds the output word, and every
  tape of `f` reads `0` from position `g` on (`called_far`).
* `cleanP` (`cleanP_exec`): erase the bank and the tally in one parallel sweep driven by `G`
  (`Control.eraseP`), then blank `G`. Every stream of the call site then reads `0` everywhere, so the next call
  starts from blank tapes.

Both phases cost a constant times `|x| + budget + 1` steps, whatever the number of tapes of `f` (`callCost`,
`cleanCost`). The states are described up to reading (`SimW`), so that the phases compose with any program that
reads the output between them.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.Control

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.PrimT.ReadEq NearCubicGates.Close.CheckedPCPP
open NearCubicGates.Close.WorkerArith (guardP tallyP clearSelfP inTape guardM tallyM clockDock clearSelfM)
open NearCubicWires.RepairSource.OrdinaryOracleCompose (clockMachine)
open NearCubicWires.WireExponent3_5.PrimAsm.DockW (updS)
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay)

variable {ns nr : ℕ}

/-- **A call site** of a program `p`: the streams `bank j` for its tapes, a tally, a guard and a ruler, all
distinct, and four registers. -/
structure Site (p : Program) (ns nr : ℕ) where
  /-- The stream of each tape of the program. -/
  bank : Fin p.tapeCount → Fin (ns + 1)
  /-- The tally of the steps of a run. -/
  tally : Fin (ns + 1)
  /-- The guard, `1^g` with `g` beyond every cell a run can reach. -/
  guard : Fin (ns + 1)
  /-- The ruler of the head resets. -/
  ruler : Fin (ns + 1)
  /-- Four scratch registers. -/
  regs : Fin 4 ↪ Fin nr
  bank_inj : Function.Injective bank
  tally_ne : ∀ j, bank j ≠ tally
  guard_ne : ∀ j, bank j ≠ guard
  ruler_ne : ∀ j, bank j ≠ ruler
  tally_guard : tally ≠ guard
  tally_ruler : tally ≠ ruler
  guard_ruler : guard ≠ ruler

namespace Site

variable {p : Program} (s : Site p ns nr)

theorem reg_ne {i j : Fin 4} (h : i ≠ j) : s.regs i ≠ s.regs j := s.regs.injective.ne h

/-- The stream of the input tape. -/
def input : Fin (ns + 1) := s.bank (inTape p)

/-- The bank and the tally, as the tapes of the erase. -/
def swept : Fin (p.tapeCount + 1) → Fin (ns + 1) :=
  Fin.addCases (motive := fun _ => Fin (ns + 1)) s.bank (fun _ : Fin 1 => s.tally)

theorem swept_injective : Function.Injective s.swept := addCases_inj s.bank s.bank_inj s.tally s.tally_ne

theorem swept_ne_guard (j : Fin (p.tapeCount + 1)) : s.swept j ≠ s.guard := by
  refine Fin.addCases (fun j' => ?_) (fun _ => ?_) j
  · simp only [swept, Fin.addCases_left]; exact s.guard_ne j'
  · simp only [swept, Fin.addCases_right]; exact s.tally_guard

theorem swept_ne_ruler (j : Fin (p.tapeCount + 1)) : s.swept j ≠ s.ruler := by
  refine Fin.addCases (fun j' => ?_) (fun _ => ?_) j
  · simp only [swept, Fin.addCases_left]; exact s.ruler_ne j'
  · simp only [swept, Fin.addCases_right]; exact s.tally_ruler

end Site

/-! ## The two phases -/

/-- **The call**: the guard `1^{2|x|+2}` from the framed input, the clocked run of the program, the tally appended
to the guard. -/
noncomputable def callP {p : Program} (s : Site p ns nr) : WMX ns nr :=
  .seq (guardP s.input s.guard (s.regs 0) (s.regs 1) (s.regs 2))
    (.seq (WMX.machZ (clockMachine p.machine) (Fin.addCases (motive := fun _ => Fin (ns + 1)) s.bank
        (fun _ : Fin 1 => s.tally)) s.ruler)
      (tallyP s.tally s.guard (s.regs 2) (s.regs 3)))

/-- **The cleanup**: the parallel erase of the bank and the tally driven by the guard, then the guard blanked. -/
noncomputable def cleanP {p : Program} (s : Site p ns nr) : WMX ns nr :=
  .seq (eraseP s.swept s.guard s.ruler) (clearSelfP s.guard (s.regs 0))

/-- The cost of the call on an input word of length `w` with budget `B`. -/
def callCost (w B : ℕ) : ℕ := 110 * (w + B + 1)

/-- The cost of the cleanup with a guard of `g` ones. -/
def cleanCost (g : ℕ) : ℕ := 22 * (g + 1)

/-- The length of the guard after a call: `2|x| + 2 + s`. -/
def guardLength (w steps : ℕ) : ℕ := 2 * w + 2 + steps

/-- The state after the call: the bank holds the exit tapes of the run, the tally `1^s`, the guard `1^g`; heads,
registers, the cell and the other streams as before. -/
noncomputable def calledState {p : Program} (s : Site p ns nr) (σ : WState ns nr) (tapes : Fin p.tapeCount → List Bool)
    (w steps : ℕ) : WState ns nr :=
  ((updS s.bank σ (fun _ => 0) tapes).sets s.tally (List.replicate steps true)).sets s.guard
    (List.replicate (guardLength w steps) true)

/-- The state after the cleanup: the bank, the tally and the guard empty; heads, registers, the cell and the other
streams as before. -/
noncomputable def cleanState {p : Program} (s : Site p ns nr) (σ : WState ns nr) : WState ns nr :=
  ((updS s.bank σ (fun _ => 0) (fun _ => [])).sets s.tally []).sets s.guard []

/-! ## The call -/

theorem blank_rdEq_any {l l' : List Bool} (h : NearCubicGates.Close.Worker.Blank l)
    (h' : NearCubicGates.Close.Worker.Blank l') : RdEq l l' := fun q => (h q).trans (h' q).symm

theorem replicate_false_blank' (m : ℕ) : NearCubicGates.Close.Worker.Blank (List.replicate m false) :=
  NearCubicGates.Close.WorkerArith.replicate_false_blank m

theorem nil_blank : NearCubicGates.Close.Worker.Blank [] := fun q => by unfold readTapeBit; simp

/-- **The call phase.** From the input tapes of `f` on the bank (all heads `0`), an empty tally and guard, a blank
ruler and zero registers, the call runs `f` within its budget: the output tape of `f` holds `output req` (at most
`s + 1` cells after `s` steps), every tape of `f` reads `0` from the guard length on, and the state reads like
`calledState`, in `callCost` steps. -/
theorem callP_exec {Request : Type} {input output : Request → List Bool} {budget : Request → ℕ}
    (f : WordFunction Request input output budget) (req : Request) (cap : ℕ) (s : Site f.program ns nr)
    (σ : WState ns nr) (hin : ∀ j, σ.st (s.bank j) = f.program.inputTapes (input req) j)
    (h0 : ∀ j, σ.sh (s.bank j) = 0) (hTL : σ.st s.tally = []) (hTLh : σ.sh s.tally = 0)
    (hG : σ.st s.guard = []) (hGh : σ.sh s.guard = 0) (hL : NearCubicGates.Close.Worker.Blank (σ.st s.ruler))
    (hLh : σ.sh s.ruler = 0) (hR : ∀ i, σ.val (s.regs i) = 0)
    (hcap : 2 * (input req).length + 2 + budget req ≤ cap) :
    ∃ (tapes : Fin f.program.tapeCount → List Bool) (steps : ℕ) (τ : WState ns nr),
      tapes f.program.outputTape = output req ∧ steps ≤ budget req ∧
      (tapes f.program.outputTape).length ≤ steps + 1 ∧
      (∀ j q, guardLength (input req).length steps ≤ q → readTapeBit (tapes j) q = false) ∧
      WXExec cap (callP s) σ τ (callCost (input req).length (budget req)) ∧
      SimW (calledState s σ tapes (input req).length steps) τ := by
  set w := (input req).length with hw
  set a := 2 * w + 2 with ha
  have hTG := s.tally_guard
  have hTR := s.tally_ruler
  have hGR := s.guard_ruler
  -- the exact start: the ruler holds `budget req` blanks
  set σ0 := σ.sets s.ruler (List.replicate (budget req) false) with hσ0
  have hs0 : SimW σ0 σ := by
    refine ⟨rfl, rfl, rfl, fun i => ?_⟩
    by_cases hi : i = s.ruler
    · subst hi; simp only [hσ0, WState.sets_st, Function.update_self]
      exact blank_rdEq_any (replicate_false_blank' _) hL
    · simp only [hσ0, WState.sets_st, Function.update_of_ne hi]; exact RdEq.refl _
  have s0st : ∀ i, i ≠ s.ruler → σ0.st i = σ.st i := fun i hi => by
    simp only [hσ0, WState.sets_st, Function.update_of_ne hi]
  -- step 1: the guard
  have hX : σ0.st s.input = frame (input req) := by
    rw [Site.input, s0st _ (s.ruler_ne _), hin]
    simp [Program.inputTapes, inTape]
  have e1 := guardM cap s.input s.guard (s.regs 0) (s.regs 1) (s.regs 2) (s.reg_ne (by decide))
    (s.reg_ne (by decide)) (s.reg_ne (by decide)) σ0 (input req) hX (by simp [hσ0, Site.input, h0])
    (s.guard_ne _) (by rw [s0st _ hGR, hG]) (by simp [hσ0, hGh]) (by simp [hσ0, hR]) (by simp [hσ0, hR])
    (by simp [hσ0, hR]) (by omega)
  set σ1 := ((σ0.sets s.guard (List.replicate a true)).seth s.guard a).setv (s.regs 2) a with hσ1
  -- step 2: the clocked run
  obtain ⟨receipt, τ2, hrun, hrout, hsteps, e2, t2tm, t2TL, t2sh, t2TLh, t2o, t2val, t2cell⟩ :=
    clockDock f req cap s.bank s.bank_inj s.tally s.ruler s.tally_ne s.ruler_ne hTR σ1
      (fun j => by
        simp only [hσ1, WState.setv_st, WState.seth_st, WState.sets_st, Function.update_of_ne (s.guard_ne j)]
        rw [s0st _ (s.ruler_ne j), hin])
      (by simp only [hσ1, WState.setv_st, WState.seth_st, WState.sets_st, Function.update_of_ne hTG]
          rw [s0st _ hTR, hTL])
      (fun j => by simp [hσ1, hσ0, Function.update_of_ne (s.guard_ne j), h0 j])
      (by simp [hσ1, hσ0, Function.update_of_ne hTG, hTLh])
      (by simp [hσ1, hσ0, Function.update_of_ne hGR.symm])
      (by simp [hσ1, hσ0, Function.update_of_ne hGR.symm, hLh])
  -- step 3: the tally
  have t2G : τ2.st s.guard = List.replicate a true ∧ τ2.sh s.guard = a := by
    obtain ⟨h1, h2⟩ := t2o s.guard s.guard_ne hTG.symm
    rw [h1, h2]; simp [hσ1]
  have e3 := tallyM cap s.tally s.guard hTG (s.regs 2) (s.regs 3) (s.reg_ne (by decide)) τ2 a receipt.steps
    t2G.1 t2G.2 (by rw [t2val]; simp [hσ1]) t2TL t2TLh
    (by rw [t2val]; simp [hσ1, Function.update_of_ne (s.reg_ne (show (3 : Fin 4) ≠ 2 by decide)), hσ0, hR])
    (by omega)
  set τ3 := ((τ2.sets s.guard (List.replicate (a + receipt.steps) true)).seth s.guard 0).setv (s.regs 2) 0
    with hτ3
  have E := WXExec.seq e1 (WXExec.seq e2 e3)
  obtain ⟨τ, eτ, hsτ⟩ := wxexec_sim E σ hs0
  -- the far blanks of the exit tapes
  have hlenF : ∀ j, (f.program.inputTapes (input req) j).length ≤ 2 * w + 1 := by
    intro j
    simp only [Program.inputTapes]
    split_ifs
    · rw [frame_length]
    · simp
  have far : ∀ j q, guardLength w receipt.steps ≤ q → readTapeBit (receipt.final.tapes j) q = false := by
    intro j q hq
    have := runFrom_far f.program.machine j (budget req) _ (f.program.inputTapes (input req) j).length receipt
      hrun (by simp [initialConfiguration]) (fun q hq => readTapeBit_beyond _ _ (by
        simp only [initialConfiguration]; omega))
    exact this.2 q (by unfold guardLength at hq; have := hlenF j; omega)
  have hlenO : (receipt.final.tapes f.program.outputTape).length ≤ receipt.steps + 1 := by
    have := NearCubicGates.Close.WorkerArith.runFrom_len f.program.machine f.program.outputTape (budget req) _ 0
      receipt hrun (by simp [initialConfiguration])
      (by simp [initialConfiguration, Program.inputTapes, f.program.outputFresh])
    omega
  refine ⟨receipt.final.tapes, receipt.steps, τ, hrout, hsteps, hlenO, far, eτ.mono ?_, SimW.trans ?_ hsτ⟩
  · unfold callCost; omega
  · -- the end state reads like `calledState`
    have hτ3st : ∀ i, τ3.st i = if i = s.guard then List.replicate (a + receipt.steps) true else τ2.st i := by
      intro i; by_cases hi : i = s.guard
      · subst hi; simp [hτ3]
      · simp [hτ3, Function.update_of_ne hi, hi]
    have hτ3sh : ∀ i, τ3.sh i = if i = s.guard then 0 else τ2.sh i := by
      intro i; by_cases hi : i = s.guard
      · subst hi; simp [hτ3]
      · simp [hτ3, Function.update_of_ne hi, hi]
    have hcs_st : ∀ i, (calledState s σ receipt.final.tapes w receipt.steps).st i =
        if i = s.guard then List.replicate (guardLength w receipt.steps) true else
        if i = s.tally then List.replicate receipt.steps true else
          (updS s.bank σ (fun _ => 0) receipt.final.tapes).st i := by
      intro i; unfold calledState
      by_cases hi : i = s.guard
      · subst hi; simp
      · by_cases hi' : i = s.tally
        · subst hi'; simp [Function.update_of_ne hi, hi]
        · simp [Function.update_of_ne hi, Function.update_of_ne hi', hi, hi']
    have hcs_sh : (calledState s σ receipt.final.tapes w receipt.steps).sh =
        (updS s.bank σ (fun _ => 0) receipt.final.tapes).sh := by
      unfold calledState; rfl
    refine ⟨?_, ?_, ?_, fun i => ?_⟩
    · funext i
      rw [hτ3sh, hcs_sh]
      by_cases hb : ∃ j, s.bank j = i
      · obtain ⟨j, rfl⟩ := hb
        rw [if_neg (s.guard_ne j), t2sh j, updS_sh_slot _ _ _ _ s.bank_inj]
      · push Not at hb
        rw [updS_sh_other _ _ _ _ i hb]
        by_cases hiG : i = s.guard
        · subst hiG; rw [if_pos rfl, hGh]
        · rw [if_neg hiG]
          by_cases hiT : i = s.tally
          · subst hiT; rw [t2TLh, hTLh]
          · rw [(t2o i hb hiT).2]
            simp [hσ1, hσ0, Function.update_of_ne hiG]
    · unfold calledState
      simp only [WState.sets_val, NearCubicGates.Close.WordPrograms.updS_val]
      funext r
      simp only [hτ3, WState.setv_val, WState.seth_val, WState.sets_val, t2val, hσ1, hσ0]
      by_cases hr : r = s.regs 2
      · subst hr; simp [hR]
      · simp [Function.update_of_ne hr]
    · unfold calledState
      simp [hτ3, t2cell, hσ1, hσ0]
    · rw [hτ3st, hcs_st]
      by_cases hiG : i = s.guard
      · subst hiG; rw [if_pos rfl, if_pos rfl]; exact RdEq.refl _
      · rw [if_neg hiG, if_neg hiG]
        by_cases hiT : i = s.tally
        · subst hiT; rw [if_pos rfl, t2TL]; exact RdEq.refl _
        · rw [if_neg hiT]
          by_cases hb : ∃ j, s.bank j = i
          · obtain ⟨j, rfl⟩ := hb
            rw [t2tm j, updS_st_slot _ _ _ _ s.bank_inj]; exact RdEq.refl _
          · push Not at hb
            rw [updS_st_other _ _ _ _ i hb, (t2o i hb hiT).1]
            simp only [hσ1, WState.setv_st, WState.seth_st, WState.sets_st, Function.update_of_ne hiG]
            exact (hs0.st i).symm

/-! ## The cleanup -/

/-- **The cleanup phase.** From a state whose bank and tally read `0` from position `g` on (heads `0`), with the
guard `1^g`, a blank ruler and a zero register, the cleanup leaves a state that reads like `cleanState`, in
`cleanCost g` steps. -/
theorem cleanP_exec {p : Program} (cap : ℕ) (s : Site p ns nr) (g : ℕ) (σ : WState ns nr)
    (hbank : ∀ j q, g ≤ q → readTapeBit (σ.st (s.bank j)) q = false) (h0 : ∀ j, σ.sh (s.bank j) = 0)
    (hTL : ∀ q, g ≤ q → readTapeBit (σ.st s.tally) q = false) (hTLh : σ.sh s.tally = 0)
    (hG : σ.st s.guard = List.replicate g true) (hGh : σ.sh s.guard = 0)
    (hL : NearCubicGates.Close.Worker.Blank (σ.st s.ruler)) (hLh : σ.sh s.ruler = 0) (hR : σ.val (s.regs 0) = 0)
    (hcap : g ≤ cap) :
    ∃ τ, WXExec cap (cleanP s) σ τ (cleanCost g) ∧ SimW (cleanState s σ) τ := by
  have hTG := s.tally_guard
  have hTR := s.tally_ruler
  have hGR := s.guard_ruler
  set σ0 := σ.sets s.ruler (List.replicate (g + 1) false) with hσ0
  have hs0 : SimW σ0 σ := by
    refine ⟨rfl, rfl, rfl, fun i => ?_⟩
    by_cases hi : i = s.ruler
    · subst hi; simp only [hσ0, WState.sets_st, Function.update_self]
      exact blank_rdEq_any (replicate_false_blank' _) hL
    · simp only [hσ0, WState.sets_st, Function.update_of_ne hi]; exact RdEq.refl _
  have s0st : ∀ i, i ≠ s.ruler → σ0.st i = σ.st i := fun i hi => by
    simp only [hσ0, WState.sets_st, Function.update_of_ne hi]
  have hsw0 : ∀ j, σ0.sh (s.swept j) = 0 := by
    intro j
    refine Fin.addCases (fun j' => ?_) (fun _ => ?_) j
    · simp [Site.swept, hσ0, h0]
    · simp [Site.swept, hσ0, hTLh]
  obtain ⟨τ1, e1, t1sw, t1sh, t1G, t1Gh, t1o, t1val, t1cell⟩ := eraseP_exec cap s.swept s.swept_injective
    s.guard s.ruler s.swept_ne_guard s.swept_ne_ruler hGR g (g + 1) σ0 hsw0 (by rw [s0st _ hGR, hG])
    (by simp [hσ0, hGh]) (by simp [hσ0]) (by simp [hσ0, hLh]) le_rfl
  have e2 := clearSelfM cap s.guard (s.regs 0) τ1 g t1G t1Gh (by rw [t1val]; simp [hσ0, hR]) hcap
  have E := WXExec.seq e1 e2
  obtain ⟨τ, eτ, hsτ⟩ := wxexec_sim E σ hs0
  refine ⟨τ, eτ.mono (by unfold cleanCost; omega), SimW.trans ?_ hsτ⟩
  -- the bank and the tally after the erase
  have hbank1 : ∀ j, τ1.st (s.bank j) = overlay (List.replicate g false) (σ.st (s.bank j)) := by
    intro j
    have := t1sw (Fin.castAdd 1 j)
    simp only [Site.swept, Fin.addCases_left] at this
    rw [this, s0st _ (s.ruler_ne j)]
  have hbank1h : ∀ j, τ1.sh (s.bank j) = 0 := by
    intro j
    have := t1sh (Fin.castAdd 1 j)
    simpa only [Site.swept, Fin.addCases_left] using this
  have hTL1 : τ1.st s.tally = overlay (List.replicate g false) (σ.st s.tally) := by
    have := t1sw (Fin.natAdd p.tapeCount (0 : Fin 1))
    simp only [Site.swept, Fin.addCases_right] at this
    rw [this, s0st _ hTR]
  have hTL1h : τ1.sh s.tally = 0 := by
    have := t1sh (Fin.natAdd p.tapeCount (0 : Fin 1))
    simpa only [Site.swept, Fin.addCases_right] using this
  have hother : ∀ i, (∀ j, s.bank j ≠ i) → i ≠ s.tally → i ≠ s.guard → τ1.st i = σ0.st i ∧ τ1.sh i = σ0.sh i := by
    intro i hb hiT hiG
    refine t1o i (fun j => ?_) hiG
    refine Fin.addCases (fun j' => ?_) (fun _ => ?_) j
    · simp only [Site.swept, Fin.addCases_left]; exact hb j'
    · simp only [Site.swept, Fin.addCases_right]; exact fun h => hiT h.symm
  have hcs_st : ∀ i, (cleanState s σ).st i = if i = s.guard then [] else if i = s.tally then [] else
      (updS s.bank σ (fun _ => 0) (fun _ => [])).st i := by
    intro i; unfold cleanState
    by_cases hi : i = s.guard
    · subst hi; simp
    · by_cases hi' : i = s.tally
      · subst hi'; simp [Function.update_of_ne hi]
      · simp [Function.update_of_ne hi, Function.update_of_ne hi', hi, hi']
  refine ⟨?_, ?_, ?_, fun i => ?_⟩
  · funext i
    show (τ1.sets s.guard (List.replicate g false)).sh i = (cleanState s σ).sh i
    simp only [WState.sets_sh]
    unfold cleanState
    simp only [WState.sets_sh]
    by_cases hb : ∃ j, s.bank j = i
    · obtain ⟨j, rfl⟩ := hb
      rw [hbank1h j, updS_sh_slot _ _ _ _ s.bank_inj]
    · push Not at hb
      rw [updS_sh_other _ _ _ _ i hb]
      by_cases hiT : i = s.tally
      · subst hiT; rw [hTL1h, hTLh]
      · by_cases hiG : i = s.guard
        · subst hiG; rw [t1Gh, hGh]
        · rw [(hother i hb hiT hiG).2]; simp [hσ0]
  · show (τ1.sets s.guard (List.replicate g false)).val = (cleanState s σ).val
    unfold cleanState
    simp only [WState.sets_val, NearCubicGates.Close.WordPrograms.updS_val, t1val, hσ0]
  · show (τ1.sets s.guard (List.replicate g false)).cell = (cleanState s σ).cell
    unfold cleanState
    simp only [WState.sets_cell, NearCubicGates.Close.WordPrograms.updS_cell, t1cell, hσ0]
  · show RdEq ((cleanState s σ).st i) ((τ1.sets s.guard (List.replicate g false)).st i)
    rw [hcs_st]
    simp only [WState.sets_st]
    by_cases hiG : i = s.guard
    · subst hiG; rw [if_pos rfl, Function.update_self]
      exact blank_rdEq_any nil_blank (replicate_false_blank' _)
    · rw [if_neg hiG, Function.update_of_ne hiG]
      by_cases hiT : i = s.tally
      · subst hiT; rw [if_pos rfl, hTL1]
        exact blank_rdEq_any nil_blank (blank_overlay g _ hTL)
      · rw [if_neg hiT]
        by_cases hb : ∃ j, s.bank j = i
        · obtain ⟨j, rfl⟩ := hb
          rw [updS_st_slot _ _ _ _ s.bank_inj, hbank1 j]
          exact blank_rdEq_any nil_blank (blank_overlay g _ (hbank j))
        · push Not at hb
          rw [updS_st_other _ _ _ _ i hb, (hother i hb hiT hiG).1]
          exact (hs0.st i).symm

end NearQuarticWires.Control
