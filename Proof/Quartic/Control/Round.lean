import Proof.Quartic.Control.Write

/-!
# One round of the seed-fixing loop

Paper: Step 3 of `sec:algorithm`, paper/paper.tex: for `i = 1, …, S`, with the current prefix `π`
of length `i − 1`, evaluate the two children `π0` and `π1` and keep the one of smaller value (ties to `0`); this is
`greedyStep R π = π ++ [decide (R (π1) < R (π0))]` (imported from `Proof.Wire_3_5.SeedFixGreedy`). `prop:time`: each round costs two child evaluations.

The program works on one layout of streams (`Layout`): the input `frame w` (`IN`), the output (`OUT`), the prefix
`marks π` (`P`), a ruler, and two call sites `A`, `B` of the child program (each a bank of its tapes, a tally and a
guard). One round (`roundP`):

1. writes the input of the child `π0` on bank `A` (`writeChild`) and calls the child there (`callP`);
2. writes the input of the child `π1` on bank `B` and calls the child there;
3. compares the two integers on the two output tapes (`ltInt`) and appends the bit to `P` (`appendBit`);
4. erases both banks (`cleanP`).

`round_exec`: from the round state of `π`, the round reaches a state that reads like the round state of
`π ++ [decide (R (π1) < R (π0))]`, in time linear in `|w| + |π|` and the two child budgets.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.Control

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.PrimT.ReadEq NearCubicGates.Close.CheckedPCPP
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat (appendO emitPair emitPair_spec appendO_st appendO_sh
  appendO_val appendO_cell)
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (read_pre)
open NearCubicWires.RepairOrdinary.Streaming (marks marks_append marks_length)
open NearCubicGates.Close.WorkerArith (inTape)
open NearCubicWires.WireExponent3_5.PrimAsm.DockW (updS)

/-! ## The layout -/

section Layout

variable (t : ℕ)

/-- The number of streams minus one: eight named streams and two banks of `t` tapes. -/
abbrev lns : ℕ := 7 + 2 * t

/-- The number of registers. -/
abbrev lnr : ℕ := 32

/-- The input `frame w`. -/
def sIN : Fin (lns t + 1) := ⟨0, by simp only [lns, lnr]; omega⟩
/-- The output. -/
def sOUT : Fin (lns t + 1) := ⟨1, by simp only [lns, lnr]; omega⟩
/-- The prefix `marks π`. -/
def sP : Fin (lns t + 1) := ⟨2, by simp only [lns, lnr]; omega⟩
/-- The ruler of all head resets. -/
def sL : Fin (lns t + 1) := ⟨3, by simp only [lns, lnr]; omega⟩
/-- The tally of site `A`. -/
def sTA : Fin (lns t + 1) := ⟨4, by simp only [lns, lnr]; omega⟩
/-- The guard of site `A`. -/
def sGA : Fin (lns t + 1) := ⟨5, by simp only [lns, lnr]; omega⟩
/-- The tally of site `B`. -/
def sTB : Fin (lns t + 1) := ⟨6, by simp only [lns, lnr]; omega⟩
/-- The guard of site `B`. -/
def sGB : Fin (lns t + 1) := ⟨7, by simp only [lns, lnr]; omega⟩
/-- Bank `A`. -/
def bankA (j : Fin t) : Fin (lns t + 1) := ⟨8 + j.val, by simp only [lns, lnr]; omega⟩
/-- Bank `B`. -/
def bankB (j : Fin t) : Fin (lns t + 1) := ⟨8 + t + j.val, by simp only [lns, lnr]; omega⟩

/-- The registers of the call sites. -/
def rS : Fin 4 ↪ Fin lnr := ⟨fun i => ⟨i.val, by simp only [lns, lnr]; omega⟩, fun a b h => Fin.ext (by simpa using congrArg Fin.val h)⟩
/-- The registers of the comparison. -/
def rG : Fin 5 ↪ Fin lnr :=
  ⟨fun i => ⟨4 + i.val, by simp only [lns, lnr]; omega⟩, fun a b h => Fin.ext (by have := congrArg Fin.val h; simp at this; omega)⟩
/-- The output counter of the writers. -/
def rOP : Fin lnr := ⟨9, by simp only [lns, lnr]; omega⟩
/-- The read counter of the writers. -/
def rC : Fin lnr := ⟨10, by simp only [lns, lnr]; omega⟩

theorem bankA_val (j : Fin t) : (bankA t j).val = 8 + j.val := rfl
theorem bankB_val (j : Fin t) : (bankB t j).val = 8 + t + j.val := rfl

theorem bankA_inj : Function.Injective (bankA t) := fun a b h => Fin.ext (by
  have := congrArg Fin.val h; simp [bankA] at this; omega)
theorem bankB_inj : Function.Injective (bankB t) := fun a b h => Fin.ext (by
  have := congrArg Fin.val h; simp [bankB] at this; omega)

/-- Two streams with different indices differ. -/
theorem ne_of_val {a b : Fin (lns t + 1)} (h : a.val ≠ b.val) : a ≠ b := fun e => h (congrArg Fin.val e)

end Layout

/-- **Site `A`** of the child program `p`. -/
def siteA (p : Program) : Site p (lns p.tapeCount) lnr where
  bank := bankA p.tapeCount
  tally := sTA p.tapeCount
  guard := sGA p.tapeCount
  ruler := sL p.tapeCount
  regs := rS
  bank_inj := bankA_inj _
  tally_ne := fun j => ne_of_val _ (by simp [bankA, sTA]; omega)
  guard_ne := fun j => ne_of_val _ (by simp [bankA, sGA]; omega)
  ruler_ne := fun j => ne_of_val _ (by simp [bankA, sL]; omega)
  tally_guard := ne_of_val _ (by simp [sTA, sGA])
  tally_ruler := ne_of_val _ (by simp [sTA, sL])
  guard_ruler := ne_of_val _ (by simp [sGA, sL])

/-- **Site `B`** of the child program `p`. -/
def siteB (p : Program) : Site p (lns p.tapeCount) lnr where
  bank := bankB p.tapeCount
  tally := sTB p.tapeCount
  guard := sGB p.tapeCount
  ruler := sL p.tapeCount
  regs := rS
  bank_inj := bankB_inj _
  tally_ne := fun j => ne_of_val _ (by simp [bankB, sTB]; omega)
  guard_ne := fun j => ne_of_val _ (by simp [bankB, sGB]; omega)
  ruler_ne := fun j => ne_of_val _ (by simp [bankB, sL]; omega)
  tally_guard := ne_of_val _ (by simp [sTB, sGB])
  tally_ruler := ne_of_val _ (by simp [sTB, sL])
  guard_ruler := ne_of_val _ (by simp [sGB, sL])


section Cases

variable (t : ℕ)

@[simp] theorem sIN_val : (sIN t).val = 0 := rfl
@[simp] theorem sOUT_val : (sOUT t).val = 1 := rfl
@[simp] theorem sP_val : (sP t).val = 2 := rfl
@[simp] theorem sL_val : (sL t).val = 3 := rfl
@[simp] theorem sTA_val : (sTA t).val = 4 := rfl
@[simp] theorem sGA_val : (sGA t).val = 5 := rfl
@[simp] theorem sTB_val : (sTB t).val = 6 := rfl
@[simp] theorem sGB_val : (sGB t).val = 7 := rfl

/-- Every stream of the layout is a named stream or a tape of one of the two banks. -/
theorem stream_cases (q : Fin (lns t + 1)) :
    q = sIN t ∨ q = sOUT t ∨ q = sP t ∨ q = sL t ∨ q = sTA t ∨ q = sGA t ∨ q = sTB t ∨ q = sGB t ∨
      (∃ j, q = bankA t j) ∨ (∃ j, q = bankB t j) := by
  have hq := q.isLt
  simp only [lns] at hq
  by_cases h8 : q.val < 8
  · have : q.val = 0 ∨ q.val = 1 ∨ q.val = 2 ∨ q.val = 3 ∨ q.val = 4 ∨ q.val = 5 ∨ q.val = 6 ∨ q.val = 7 := by omega
    rcases this with h | h | h | h | h | h | h | h
    all_goals first
      | exact Or.inl (Fin.ext h)
      | exact Or.inr (Or.inl (Fin.ext h))
      | exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
      | exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h)))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h))))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h)))))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h))))))))
  · right; right; right; right; right; right; right; right
    by_cases hA : q.val < 8 + t
    · left; exact ⟨⟨q.val - 8, by omega⟩, Fin.ext (by simp [bankA]; omega)⟩
    · right; exact ⟨⟨q.val - 8 - t, by omega⟩, Fin.ext (by simp [bankB]; omega)⟩

end Cases

/-! ## Appending a bit to the prefix -/

section Append

variable {ns nr : ℕ} (cap : ℕ)

/-- Walk to the end of `marks π` on `P`, counting the cells in `C`. -/
def walkLoop (P : Fin (ns + 1)) (C : Fin nr) : WMX ns nr :=
  .whs P (.seq (WMX.fwd P) (.seq (WMX.fwd P) (.seq (WMX.inc C) (WMX.inc C))))

theorem walkLoop_exec (σ : WState ns nr) (P : Fin (ns + 1)) (C : Fin nr) (π : List Bool) (hP : σ.st P = marks π)
    (hPh : σ.sh P = 0) (hC : σ.val C = 0) (hc : 2 * π.length + 2 ≤ cap) :
    WXExec cap (walkLoop P C) σ ((σ.seth P (2 * π.length)).setv C (2 * π.length)) (π.length * 13 + 1) := by
  have key : ∀ m k, k + m = π.length →
      WXExec cap (walkLoop P C) ((σ.seth P (2 * k)).setv C (2 * k))
        ((σ.seth P (2 * π.length)).setv C (2 * π.length)) (m * 13 + 1) := by
    intro m
    induction m with
    | zero =>
      intro k hk
      rw [Nat.add_zero] at hk; subst hk
      refine WXExec.mono (WXExec.whsF ?_) (by omega)
      simp only [wbit, WState.setv_st, WState.seth_st, WState.setv_sh, WState.seth_sh, Function.update_self, hP]
      have := read_marks_end π [] (by rfl)
      simpa using this
    | succ m ih =>
      intro k hk
      have hb : wbit ((σ.seth P (2 * k)).setv C (2 * k)) P = true := by
        simp only [wbit, WState.setv_st, WState.seth_st, WState.setv_sh, WState.seth_sh, Function.update_self, hP]
        have := read_marks_mark π [] k (by omega)
        simpa using this
      set τ0 := (σ.seth P (2 * k)).setv C (2 * k) with hτ0
      have e1 := WXExec.fwd cap P τ0
      have e2 := WXExec.fwd cap P (τ0.seth P (τ0.sh P + 1))
      set τ2 := (τ0.seth P (τ0.sh P + 1)).seth P ((τ0.seth P (τ0.sh P + 1)).sh P + 1) with hτ2
      have e3 := WXExec.inc cap C τ2 (by simp [hτ2, hτ0]; omega)
      have e4 := WXExec.inc cap C (τ2.setv C (τ2.val C + 1)) (by simp [hτ2, hτ0]; omega)
      have e5 := ih (k + 1) (by omega)
      have hstate : (τ2.setv C (τ2.val C + 1)).setv C ((τ2.setv C (τ2.val C + 1)).val C + 1) =
          (σ.seth P (2 * (k + 1))).setv C (2 * (k + 1)) := by
        refine WState.eq ?_ rfl ?_ rfl
        · funext q; by_cases hq : q = P
          · subst hq; simp [hτ2, hτ0]; omega
          · simp [hτ2, hτ0, Function.update_of_ne hq]
        · funext q; by_cases hq : q = C
          · subst hq; simp [hτ2, hτ0]; omega
          · simp [hτ2, hτ0, Function.update_of_ne hq]
      rw [hstate] at e4
      exact WXExec.mono (WXExec.whsT hb (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 e4))) e5) (by ring_nf; omega)
  have h := key π.length 0 (by omega)
  have h0 : (σ.seth P (2 * 0)).setv C (2 * 0) = σ := by
    refine WState.eq ?_ rfl ?_ rfl
    · funext q; by_cases hq : q = P
      · subst hq; simp [hPh]
      · simp [Function.update_of_ne hq]
    · funext q; by_cases hq : q = C
      · subst hq; simp [hC]
      · simp [Function.update_of_ne hq]
  rwa [h0] at h

theorem clrR_exec (σ : WState ns nr) (R : Fin nr) (hR : σ.val R ≤ 1) (hc : 1 ≤ cap) :
    WXExec cap (clrR R) σ (σ.setv R 0) 2 := by
  by_cases h0 : σ.val R = 0
  · refine WXExec.mono (WXExec.ifrF h0 (WXExec.cast cap (WXExec.skip cap σ) ?_ le_rfl)) (by omega)
    exact (BinW.setv_same h0).symm
  · have e := WXExec.dec cap R σ (by omega)
    have : σ.val R - 1 = 0 := by omega
    rw [this] at e
    exact WXExec.mono (WXExec.ifrT h0 e) (by omega)

/-- **Append a bit**: `marks π` on `P` becomes `marks (π ++ [r])`, where `r` is the bit held by the register `R`;
then `R := 0`. -/
def appendBit (P : Fin (ns + 1)) (C R : Fin nr) : WMX ns nr :=
  .seq (walkLoop P C)
  (.seq (.ifr R (.wm (emitPair P C true)) (.wm (emitPair P C false)))
  (.seq (.wm (NearCubicGates.Close.Codec.rewindLoop P C)) (clrR R)))

theorem appendBit_exec (σ : WState ns nr) (P : Fin (ns + 1)) (C R : Fin nr) (hCR : C ≠ R) (π : List Bool) (r : Bool)
    (hP : σ.st P = marks π) (hPh : σ.sh P = 0) (hC : σ.val C = 0) (hR : σ.val R = r.toNat)
    (hc : 2 * π.length + 4 ≤ cap) :
    WXExec cap (appendBit P C R) σ ((σ.sets P (marks (π ++ [r]))).setv R 0) (25 * π.length + 40) := by
  have e1 := walkLoop_exec cap σ P C π hP hPh hC (by omega)
  set σ1 := (σ.seth P (2 * π.length)).setv C (2 * π.length) with hσ1
  have hσ1P : σ1.sh P = (σ1.st P).length := by simp [hσ1, hP, marks_length]
  have e2 := emitPair_spec cap P C r σ1 hσ1P (by simp [hσ1]; omega)
  have e2' : WXExec cap (.ifr R (.wm (emitPair P C true)) (.wm (emitPair P C false))) σ1
      (appendO σ1 P C [true, r]) 16 := by
    cases r
    · exact WXExec.ifrF (by simp [hσ1, Function.update_of_ne hCR.symm, hR]) (WXExec.wm e2)
    · exact WXExec.ifrT (by simp [hσ1, Function.update_of_ne hCR.symm, hR]) (WXExec.wm e2)
  set σ2 := appendO σ1 P C [true, r] with hσ2
  have e3 := NearCubicGates.Close.Codec.rewindLoop_spec cap P C (2 * π.length + 2) σ2 (by simp [hσ2, hσ1])
    (by simp [hσ2, hσ1]) (by omega)
  set σ3 := (σ2.setv C 0).seth P (σ2.sh P - (2 * π.length + 2)) with hσ3
  have e4 := clrR_exec cap σ3 R (by simp [hσ3, hσ2, hσ1, Function.update_of_ne hCR.symm, hR]; cases r <;> simp)
    (by omega)
  refine WXExec.mono (WXExec.cast cap (WXExec.seq e1 (WXExec.seq e2' (WXExec.seq (WXExec.wm e3) e4))) ?_ le_rfl)
    (by omega)
  refine WState.eq ?_ ?_ ?_ rfl
  · funext q; by_cases hq : q = P
    · subst hq; simp [hσ3, hσ2, hσ1, hPh]
    · simp [hσ3, hσ2, hσ1, Function.update_of_ne hq]
  · funext q; by_cases hq : q = P
    · subst hq; simp [hσ3, hσ2, hσ1, hP, marks]
    · simp [hσ3, hσ2, hσ1, Function.update_of_ne hq]
  · funext q
    by_cases hqR : q = R
    · subst hqR; simp
    · by_cases hqC : q = C
      · subst hqC; simp [hσ3, hσ2, hσ1, Function.update_of_ne hqR, hC]
      · simp [hσ3, hσ2, hσ1, Function.update_of_ne hqR, Function.update_of_ne hqC]

end Append


/-! ## Reading the states of a call site -/

section SiteStates

variable {ns nr : ℕ} {p : Program} (s : Site p ns nr) (σ : WState ns nr)

/-- A stream outside the call site. -/
def Site.Out (q : Fin (ns + 1)) : Prop := (∀ j, s.bank j ≠ q) ∧ q ≠ s.tally ∧ q ≠ s.guard

theorem calledState_out (tp : Fin p.tapeCount → List Bool) (w st : ℕ) (q : Fin (ns + 1)) (hq : s.Out q) :
    (calledState s σ tp w st).st q = σ.st q ∧ (calledState s σ tp w st).sh q = σ.sh q := by
  obtain ⟨hb, ht, hg⟩ := hq
  unfold calledState
  simp only [WState.sets_st, WState.sets_sh, Function.update_of_ne hg, Function.update_of_ne ht]
  exact ⟨updS_st_other _ _ _ _ q hb, updS_sh_other _ _ _ _ q hb⟩

theorem calledState_bank (tp : Fin p.tapeCount → List Bool) (w st : ℕ) (j : Fin p.tapeCount) :
    (calledState s σ tp w st).st (s.bank j) = tp j ∧ (calledState s σ tp w st).sh (s.bank j) = 0 := by
  unfold calledState
  simp only [WState.sets_st, WState.sets_sh, Function.update_of_ne (s.guard_ne j), Function.update_of_ne (s.tally_ne j)]
  exact ⟨updS_st_slot _ _ _ _ s.bank_inj j, updS_sh_slot _ _ _ _ s.bank_inj j⟩

theorem calledState_tally (tp : Fin p.tapeCount → List Bool) (w st : ℕ) :
    (calledState s σ tp w st).st s.tally = List.replicate st true ∧
      (calledState s σ tp w st).sh s.tally = σ.sh s.tally := by
  unfold calledState
  simp only [WState.sets_st, WState.sets_sh, Function.update_of_ne s.tally_guard, Function.update_self]
  refine ⟨by simp, updS_sh_other _ _ _ _ _ s.tally_ne⟩

theorem calledState_guard (tp : Fin p.tapeCount → List Bool) (w st : ℕ) :
    (calledState s σ tp w st).st s.guard = List.replicate (guardLength w st) true ∧
      (calledState s σ tp w st).sh s.guard = σ.sh s.guard := by
  unfold calledState
  simp only [WState.sets_st, WState.sets_sh, Function.update_self]
  refine ⟨by simp, updS_sh_other _ _ _ _ _ s.guard_ne⟩

@[simp] theorem calledState_val (tp : Fin p.tapeCount → List Bool) (w st : ℕ) :
    (calledState s σ tp w st).val = σ.val := rfl

@[simp] theorem calledState_cell (tp : Fin p.tapeCount → List Bool) (w st : ℕ) :
    (calledState s σ tp w st).cell = σ.cell := rfl

theorem cleanState_out (q : Fin (ns + 1)) (hq : s.Out q) :
    (cleanState s σ).st q = σ.st q ∧ (cleanState s σ).sh q = σ.sh q := by
  obtain ⟨hb, ht, hg⟩ := hq
  unfold cleanState
  simp only [WState.sets_st, WState.sets_sh, Function.update_of_ne hg, Function.update_of_ne ht]
  exact ⟨updS_st_other _ _ _ _ q hb, updS_sh_other _ _ _ _ q hb⟩

theorem cleanState_bank (j : Fin p.tapeCount) :
    (cleanState s σ).st (s.bank j) = [] ∧ (cleanState s σ).sh (s.bank j) = 0 := by
  unfold cleanState
  simp only [WState.sets_st, WState.sets_sh, Function.update_of_ne (s.guard_ne j), Function.update_of_ne (s.tally_ne j)]
  exact ⟨updS_st_slot _ _ _ _ s.bank_inj j, updS_sh_slot _ _ _ _ s.bank_inj j⟩

theorem cleanState_tally : (cleanState s σ).st s.tally = [] ∧ (cleanState s σ).sh s.tally = σ.sh s.tally := by
  unfold cleanState
  simp only [WState.sets_st, WState.sets_sh, Function.update_of_ne s.tally_guard, Function.update_self]
  refine ⟨by simp, updS_sh_other _ _ _ _ _ s.tally_ne⟩

theorem cleanState_guard : (cleanState s σ).st s.guard = [] ∧ (cleanState s σ).sh s.guard = σ.sh s.guard := by
  unfold cleanState
  simp only [WState.sets_st, WState.sets_sh, Function.update_self]
  refine ⟨by simp, updS_sh_other _ _ _ _ _ s.guard_ne⟩

@[simp] theorem cleanState_val : (cleanState s σ).val = σ.val := rfl

@[simp] theorem cleanState_cell : (cleanState s σ).cell = σ.cell := rfl

end SiteStates

section LayoutOut

variable (p : Program)

theorem outA (q : Fin (lns p.tapeCount + 1)) (h : q.val < 4 ∨ q.val = 6 ∨ q.val = 7 ∨ 8 + p.tapeCount ≤ q.val) :
    (siteA p).Out q := by
  refine ⟨fun j hj => ?_, fun hj => ?_, fun hj => ?_⟩
  · have := congrArg Fin.val hj; simp [siteA, bankA] at this; omega
  · have := congrArg Fin.val hj; simp [siteA] at this; omega
  · have := congrArg Fin.val hj; simp [siteA] at this; omega

theorem outB (q : Fin (lns p.tapeCount + 1)) (h : q.val < 6 ∨ (8 ≤ q.val ∧ q.val < 8 + p.tapeCount)) :
    (siteB p).Out q := by
  refine ⟨fun j hj => ?_, fun hj => ?_, fun hj => ?_⟩
  · have := congrArg Fin.val hj; simp [siteB, bankB] at this; omega
  · have := congrArg Fin.val hj; simp [siteB] at this; omega
  · have := congrArg Fin.val hj; simp [siteB] at this; omega

end LayoutOut

/-! ## The round -/

/-- **The state of the loop** before a round, apart from the prefix: the input `frame w`, empty banks, tallies,
guards and ruler, all heads at `0` (the output and the round counter are free), the registers of the round at
`0`. -/
structure LoopReady (t : ℕ) (ρ : WState (lns t) lnr) (w : List Bool) : Prop where
  inp : ρ.st (sIN t) = frame w
  inph : ρ.sh (sIN t) = 0
  ph : ρ.sh (sP t) = 0
  ruler : ρ.st (sL t) = []
  rulerh : ρ.sh (sL t) = 0
  bA : ∀ j, ρ.st (bankA t j) = []
  bAh : ∀ j, ρ.sh (bankA t j) = 0
  bB : ∀ j, ρ.st (bankB t j) = []
  bBh : ∀ j, ρ.sh (bankB t j) = 0
  tA : ρ.st (sTA t) = []
  tAh : ρ.sh (sTA t) = 0
  gA : ρ.st (sGA t) = []
  gAh : ρ.sh (sGA t) = 0
  tB : ρ.st (sTB t) = []
  tBh : ρ.sh (sTB t) = 0
  gB : ρ.st (sGB t) = []
  gBh : ρ.sh (sGB t) = 0
  rs : ∀ i, ρ.val (rS i) = 0
  rg : ∀ i, ρ.val (rG i) = 0
  op : ρ.val rOP = 0
  c : ρ.val rC = 0

/-- The round state of the prefix `π`: the loop state with `marks π` on `P`. -/
def roundSt {t : ℕ} (ρ : WState (lns t) lnr) (π : List Bool) : WState (lns t) lnr := ρ.sets (sP t) (marks π)

/-- **One round** of Step 3 for the child program `p`. -/
noncomputable def roundP (p : Program) : WMX (lns p.tapeCount) lnr :=
  .seq (writeChild false (sIN _) (sP _) (siteA p).input rOP rC)
  (.seq (callP (siteA p))
  (.seq (writeChild true (sIN _) (sP _) (siteB p).input rOP rC)
  (.seq (callP (siteB p))
  (.seq (ltInt (bankA _ p.outputTape) (bankB _ p.outputTape) rG)
  (.seq (appendBit (sP _) rC (rG 4))
  (.seq (cleanP (siteA p)) (cleanP (siteB p))))))))

/-- The cost bound of a round. -/
def roundCost (w π B : ℕ) : ℕ := 2000 * (w + π + B + 2)

theorem intWord_length (z : ℤ) :
    (NearCubicGates.Close.Interfaces.intWord z).length = 3 + 2 * natBitLength z.natAbs + 1 := by
  rw [intWord_eq]; simp [NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_length]; ring

theorem frame_append_length (w π : List Bool) (b : Bool) :
    (w ++ frame (π ++ [b])).length = w.length + 2 * π.length + 3 := by
  simp [frame_length]; ring


theorem blank_nil' : NearCubicGates.Close.Worker.Blank ([] : List Bool) := fun q => by unfold readTapeBit; simp

/-- Two streams of the layout differ (by their indices). -/
local macro "dst" : tactic =>
  `(tactic| (apply ne_of_val; simp [Site.input, siteA, siteB, bankA, bankB, inTape] <;> omega))

/-- A stream lies outside a call site (by its index). -/
local macro "outs" : tactic => `(tactic| (simp [bankA, bankB] <;> omega))

/-- **One round.** From the round state of `π`, with the child word function `f` (values `R`) and its two requests
`r0`, `r1` on the children `π0`, `π1` (inputs `w ++ frame (π ++ [b])`, budgets at most `B`), the round reaches a state
that reads like the round state of `π ++ [decide (R r1 < R r0)]` (`greedyStep`), in `roundCost` steps. -/
theorem round_exec {Request : Type} {input : Request → List Bool} {Rv : Request → ℤ} {budget : Request → ℕ}
    (f : WordFunction Request input (fun r => NearCubicGates.Close.Interfaces.intWord (Rv r)) budget)
    (cap : ℕ) (ρ : WState (lns f.program.tapeCount) lnr) (w π : List Bool) (hρ : LoopReady f.program.tapeCount ρ w)
    (r0 r1 : Request) (h0 : input r0 = w ++ frame (π ++ [false])) (h1 : input r1 = w ++ frame (π ++ [true]))
    (B : ℕ) (hB0 : budget r0 ≤ B) (hB1 : budget r1 ≤ B) (hcap : 10 * (w.length + π.length + B + 10) ≤ cap) :
    ∃ τ, WXExec cap (roundP f.program) (roundSt ρ π) τ (roundCost w.length π.length B) ∧
      SimW (roundSt ρ (π ++ [decide (Rv r1 < Rv r0)])) τ := by
  have ht2 := f.program.twoTapes
  set bit := decide (Rv r1 < Rv r0) with hbit
  have hin0 : (input r0).length = w.length + 2 * π.length + 3 := by rw [h0, frame_append_length]
  have hin1 : (input r1).length = w.length + 2 * π.length + 3 := by rw [h1, frame_append_length]
  have hIP : sIN f.program.tapeCount ≠ sP f.program.tapeCount := by dst
  have hIXA : sIN f.program.tapeCount ≠ (siteA f.program).input := by dst
  have hPXA : sP f.program.tapeCount ≠ (siteA f.program).input := by dst
  have hIXB : sIN f.program.tapeCount ≠ (siteB f.program).input := by dst
  have hPXB : sP f.program.tapeCount ≠ (siteB f.program).input := by dst
  have hOC : rOP ≠ rC := by decide
  have hCR : rC ≠ rG 4 := by decide
  have hAB : bankA f.program.tapeCount f.program.outputTape ≠ bankB f.program.tapeCount f.program.outputTape := by
    dst
  have hAinB : ∀ j, (siteA f.program).input ≠ bankB f.program.tapeCount j := fun j => by dst
  have hBinA : ∀ j, (siteB f.program).input ≠ bankA f.program.tapeCount j := fun j => by dst
  have hBA : (siteB f.program).input ≠ (siteA f.program).input := by dst
  -- the round state
  set σ0 := roundSt ρ π with hσ0
  have s0st : ∀ q, q ≠ sP f.program.tapeCount → σ0.st q = ρ.st q := fun q hq => by
    simp [hσ0, roundSt, Function.update_of_ne hq]
  have s0P : σ0.st (sP f.program.tapeCount) = marks π := by simp [hσ0, roundSt]
  -- 1. the input of `π0` on bank `A`
  have hAin0 : σ0.st (siteA f.program).input = [] := by rw [s0st _ hPXA.symm]; exact hρ.bA _
  have hAin0h : σ0.sh (siteA f.program).input = 0 := hρ.bAh _
  have e1 := writeChild_exec cap σ0 false (sIN _) (sP _) (siteA f.program).input rOP rC hIP hIXA hPXA hOC w π
    (by rw [s0st _ hIP]; exact hρ.inp) hρ.inph s0P hρ.ph hAin0 hAin0h hρ.op hρ.c (by omega)
  set σ1 := σ0.sets (siteA f.program).input (frame (w ++ frame (π ++ [false]))) with hσ1
  have s1st : ∀ q, q ≠ (siteA f.program).input → q ≠ sP f.program.tapeCount → σ1.st q = ρ.st q := fun q h1 h2 => by
    simp [hσ1, Function.update_of_ne h1, s0st q h2]
  have s1sh : σ1.sh = ρ.sh := rfl
  have s1val : σ1.val = ρ.val := rfl
  -- 2. the call on bank `A`
  have hin2 : ∀ j, σ1.st ((siteA f.program).bank j) = f.program.inputTapes (input r0) j := by
    intro j
    by_cases hj : j = inTape f.program
    · subst hj
      simp only [hσ1, WState.sets_st, Site.input, Function.update_self, h0]
      simp [Program.inputTapes, inTape]
    · have hne : (siteA f.program).bank j ≠ (siteA f.program).input :=
        fun h => hj ((siteA f.program).bank_inj h)
      have hneP : (siteA f.program).bank j ≠ sP f.program.tapeCount := by dst
      rw [s1st _ hne hneP]
      have hv : ¬ (j.val = 0) := fun h => hj (Fin.ext h)
      simp only [siteA, hρ.bA, Program.inputTapes]
      rw [if_neg hv]
  have hTA1 : σ1.st (siteA f.program).tally = [] := by
    rw [s1st _ (by dst) (by dst)]; exact hρ.tA
  have hGA1 : σ1.st (siteA f.program).guard = [] := by
    rw [s1st _ (by dst) (by dst)]; exact hρ.gA
  have hL1 : NearCubicGates.Close.Worker.Blank (σ1.st (siteA f.program).ruler) := by
    rw [s1st _ (by dst) (by dst)]; simp only [siteA, hρ.ruler]; exact blank_nil'
  obtain ⟨tA, sA, τ2, houtA, hsA, hlenA, farA, e2, sim2⟩ := callP_exec f r0 cap (siteA f.program) σ1 hin2
    (fun j => hρ.bAh j) hTA1 hρ.tAh hGA1 hρ.gAh hL1 hρ.rulerh (fun i => hρ.rs i) (by rw [hin0]; omega)
  set ι2 := calledState (siteA f.program) σ1 tA (input r0).length sA with hι2
  have i2out : ∀ q, (siteA f.program).Out q → ι2.st q = σ1.st q ∧ ι2.sh q = σ1.sh q :=
    fun q hq => calledState_out _ _ _ _ _ q hq
  have i2val : ι2.val = ρ.val := rfl
  -- 3. the input of `π1` on bank `B`
  have oIN : (siteA f.program).Out (sIN f.program.tapeCount) := outA _ _ (by simp)
  have oP : (siteA f.program).Out (sP f.program.tapeCount) := outA _ _ (by simp)
  have oBin : (siteA f.program).Out (siteB f.program).input := outA _ _ (by simp [Site.input, siteB, bankB])
  have hI2 : ι2.st (sIN _) = frame w := by rw [(i2out _ oIN).1, s1st _ hIXA hIP]; exact hρ.inp
  have hI2h : ι2.sh (sIN _) = 0 := by rw [(i2out _ oIN).2, s1sh]; exact hρ.inph
  have hP2 : ι2.st (sP _) = marks π := by rw [(i2out _ oP).1]; simp [hσ1, Function.update_of_ne hPXA, s0P]
  have hP2h : ι2.sh (sP _) = 0 := by rw [(i2out _ oP).2, s1sh]; exact hρ.ph
  have hB2 : ι2.st (siteB f.program).input = [] := by
    rw [(i2out _ oBin).1, s1st _ hBA (by dst)]; exact hρ.bB _
  have hB2h : ι2.sh (siteB f.program).input = 0 := by rw [(i2out _ oBin).2, s1sh]; exact hρ.bBh _
  have e3 := writeChild_exec cap ι2 true (sIN _) (sP _) (siteB f.program).input rOP rC hIP hIXB hPXB hOC w π
    hI2 hI2h hP2 hP2h hB2 hB2h (by rw [i2val]; exact hρ.op) (by rw [i2val]; exact hρ.c) (by omega)
  set σ3 := ι2.sets (siteB f.program).input (frame (w ++ frame (π ++ [true]))) with hσ3
  have s3st : ∀ q, q ≠ (siteB f.program).input → σ3.st q = ι2.st q := fun q h => by
    simp [hσ3, Function.update_of_ne h]
  have s3sh : σ3.sh = ι2.sh := rfl
  have s3val : σ3.val = ρ.val := rfl
  -- 4. the call on bank `B`
  have outAB : ∀ q, (siteA f.program).Out q → q ≠ (siteB f.program).input → q ≠ (siteA f.program).input →
      q ≠ sP f.program.tapeCount → σ3.st q = ρ.st q ∧ σ3.sh q = ρ.sh q := by
    intro q hA hB hA' hP
    rw [s3st _ hB, (i2out _ hA).1, s1st _ hA' hP, s3sh, (i2out _ hA).2, s1sh]
    exact ⟨rfl, rfl⟩
  have hin4 : ∀ j, σ3.st ((siteB f.program).bank j) = f.program.inputTapes (input r1) j := by
    intro j
    by_cases hj : j = inTape f.program
    · subst hj
      simp only [hσ3, WState.sets_st, Site.input, Function.update_self, h1]
      simp [Program.inputTapes, inTape]
    · have hne : (siteB f.program).bank j ≠ (siteB f.program).input :=
        fun h => hj ((siteB f.program).bank_inj h)
      rw [(outAB _ (outA _ _ (by simp [siteB, bankB])) hne (by dst) (by dst)).1]
      have hv : ¬ (j.val = 0) := fun h => hj (Fin.ext h)
      simp only [siteB, hρ.bB, Program.inputTapes]
      rw [if_neg hv]
  have oTB := outAB (sTB _) (outA _ _ (by simp)) (by dst) (by dst) (by dst)
  have oGB := outAB (sGB _) (outA _ _ (by simp)) (by dst) (by dst) (by dst)
  have oL := outAB (sL _) (outA _ _ (by simp)) (by dst) (by dst) (by dst)
  obtain ⟨tB, sB, τ4, houtB, hsB, hlenB, farB, e4, sim4⟩ := callP_exec f r1 cap (siteB f.program) σ3 hin4
    (fun j => by rw [s3sh, (i2out _ (outA _ _ (by simp [siteB, bankB]))).2, s1sh]; exact hρ.bBh j)
    (by simp only [siteB]; rw [oTB.1]; exact hρ.tB) (by simp only [siteB]; rw [oTB.2]; exact hρ.tBh)
    (by simp only [siteB]; rw [oGB.1]; exact hρ.gB) (by simp only [siteB]; rw [oGB.2]; exact hρ.gBh)
    (by simp only [siteB]; rw [oL.1, hρ.ruler]; exact blank_nil') (by simp only [siteB]; rw [oL.2]; exact hρ.rulerh)
    (fun i => by rw [s3val]; exact hρ.rs i) (by rw [hin1]; omega)
  set ι4 := calledState (siteB f.program) σ3 tB (input r1).length sB with hι4
  have i4out : ∀ q, (siteB f.program).Out q → ι4.st q = σ3.st q ∧ ι4.sh q = σ3.sh q :=
    fun q hq => calledState_out _ _ _ _ _ q hq
  have i4val : ι4.val = ρ.val := rfl
  -- the two values
  have oAout : (siteB f.program).Out (bankA f.program.tapeCount f.program.outputTape) := outB _ _ (by outs)
  have hA4 : ι4.st (bankA _ f.program.outputTape) = tA f.program.outputTape := by
    rw [(i4out _ oAout).1, s3st _ (hBinA _).symm]
    exact (calledState_bank (siteA f.program) σ1 tA _ _ _).1
  have hA4h : ι4.sh (bankA _ f.program.outputTape) = 0 := by
    rw [(i4out _ oAout).2, s3sh]
    exact (calledState_bank (siteA f.program) σ1 tA _ _ _).2
  have hB4 : ι4.st (bankB _ f.program.outputTape) = tB f.program.outputTape :=
    (calledState_bank (siteB f.program) σ3 tB _ _ _).1
  have hB4h : ι4.sh (bankB _ f.program.outputTape) = 0 :=
    (calledState_bank (siteB f.program) σ3 tB _ _ _).2
  have hLa : 2 * natBitLength (Rv r0).natAbs ≤ B := by
    have := intWord_length (Rv r0); rw [← houtA] at this; omega
  have hLb : 2 * natBitLength (Rv r1).natAbs ≤ B := by
    have := intWord_length (Rv r1); rw [← houtB] at this; omega
  -- 5. the comparison
  have e5 := ltInt_exec cap ι4 (bankA _ f.program.outputTape) (bankB _ f.program.outputTape) rG hAB (pA := [])
    (rA := []) (pB := []) (rB := []) (Rv r0) (Rv r1) (by rw [hA4, houtA]; simp) (by rw [hA4h]; rfl)
    (by rw [hB4, houtB]; simp) (by rw [hB4h]; rfl) (fun i => by rw [i4val]; exact hρ.rg i) (by omega)
  set σ5 := ι4.setv (rG 4) bit.toNat with hσ5
  -- the prefix through the round
  have oPB : (siteB f.program).Out (sP f.program.tapeCount) := outB _ _ (by simp)
  have hP4 : ι4.st (sP _) = marks π := by rw [(i4out _ oPB).1, s3st _ hPXB, hP2]
  have hP4h : ι4.sh (sP _) = 0 := by rw [(i4out _ oPB).2, s3sh, hP2h]
  -- 6. the bit
  have e6 := appendBit_exec cap σ5 (sP _) rC (rG 4) hCR π bit (by simp [hσ5, hP4]) (by simp [hσ5, hP4h])
    (by simp [hσ5, hCR, i4val, hρ.c]) (by simp [hσ5]) (by omega)
  set σ6 := (σ5.sets (sP f.program.tapeCount) (marks (π ++ [bit]))).setv (rG 4) 0 with hσ6
  have s6st : ∀ q, q ≠ sP f.program.tapeCount → σ6.st q = ι4.st q := fun q h => by
    simp [hσ6, hσ5, Function.update_of_ne h]
  have s6sh : σ6.sh = ι4.sh := rfl
  have s6val : σ6.val = ρ.val := by
    funext r; by_cases hr : r = rG 4
    · subst hr; simp [hσ6, hρ.rg 4]
    · simp [hσ6, hσ5, Function.update_of_ne hr, i4val]
  -- site `A` in `σ6`
  have oTA : (siteB f.program).Out (sTA f.program.tapeCount) := outB _ _ (by simp)
  have oGA : (siteB f.program).Out (sGA f.program.tapeCount) := outB _ _ (by simp)
  have oLB : (siteB f.program).Out (sL f.program.tapeCount) := outB _ _ (by simp)
  have hA6 : ∀ j, σ6.st (bankA _ j) = tA j := by
    intro j
    rw [s6st _ (by dst), (i4out _ (outB _ _ (by outs))).1, s3st _ (hBinA _).symm]
    exact (calledState_bank (siteA f.program) σ1 tA _ _ _).1
  have hA6h : ∀ j, σ6.sh (bankA _ j) = 0 := by
    intro j
    rw [s6sh, (i4out _ (outB _ _ (by outs))).2, s3sh]
    exact (calledState_bank (siteA f.program) σ1 tA _ _ _).2
  have hTA6 : σ6.st (sTA _) = List.replicate sA true := by
    rw [s6st _ (by dst), (i4out _ oTA).1, s3st _ (by dst)]
    exact (calledState_tally (siteA f.program) σ1 tA _ _).1
  have hTA6h : σ6.sh (sTA _) = 0 := by
    rw [s6sh, (i4out _ oTA).2, s3sh]; exact (calledState_tally (siteA f.program) σ1 tA _ _).2.trans hρ.tAh
  have hGA6 : σ6.st (sGA _) = List.replicate (guardLength (input r0).length sA) true := by
    rw [s6st _ (by dst), (i4out _ oGA).1, s3st _ (by dst)]
    exact (calledState_guard (siteA f.program) σ1 tA _ _).1
  have hGA6h : σ6.sh (sGA _) = 0 := by
    rw [s6sh, (i4out _ oGA).2, s3sh]; exact (calledState_guard (siteA f.program) σ1 tA _ _).2.trans hρ.gAh
  have hL6 : σ6.st (sL _) = [] := by
    rw [s6st _ (by dst), (i4out _ oLB).1, oL.1]; exact hρ.ruler
  have hL6h : σ6.sh (sL _) = 0 := by rw [s6sh, (i4out _ oLB).2, oL.2]; exact hρ.rulerh
  -- 7. erase site `A`
  obtain ⟨τ7, e7, sim7⟩ := cleanP_exec cap (siteA f.program) (guardLength (input r0).length sA) σ6
    (fun j q hq => by simp only [siteA]; rw [hA6]; exact farA j q hq) (fun j => hA6h j)
    (fun q hq => by
      simp only [siteA]; rw [hTA6]; exact readTapeBit_beyond _ _ (by simp [guardLength] at hq ⊢; omega))
    hTA6h hGA6 hGA6h (by simp only [siteA]; rw [hL6]; exact blank_nil') hL6h
    (by rw [s6val]; exact hρ.rs 0) (by unfold guardLength; omega)
  set σ7 := cleanState (siteA f.program) σ6 with hσ7
  have s7out : ∀ q, (siteA f.program).Out q → σ7.st q = σ6.st q ∧ σ7.sh q = σ6.sh q :=
    fun q hq => cleanState_out _ _ q hq
  -- site `B` in `σ7`
  have oTB' : (siteA f.program).Out (sTB f.program.tapeCount) := outA _ _ (by simp)
  have oGB' : (siteA f.program).Out (sGB f.program.tapeCount) := outA _ _ (by simp)
  have oL' : (siteA f.program).Out (sL f.program.tapeCount) := outA _ _ (by simp)
  have hB7 : ∀ j, σ7.st (bankB _ j) = tB j := by
    intro j
    rw [(s7out _ (outA _ _ (by outs))).1, s6st _ (by dst)]
    exact (calledState_bank (siteB f.program) σ3 tB _ _ _).1
  have hB7h : ∀ j, σ7.sh (bankB _ j) = 0 := by
    intro j
    rw [(s7out _ (outA _ _ (by outs))).2, s6sh]
    exact (calledState_bank (siteB f.program) σ3 tB _ _ _).2
  have hTB7 : σ7.st (sTB _) = List.replicate sB true := by
    rw [(s7out _ oTB').1, s6st _ (by dst)]
    exact (calledState_tally (siteB f.program) σ3 tB _ _).1
  have hTB7h : σ7.sh (sTB _) = 0 := by
    rw [(s7out _ oTB').2, s6sh]
    exact (calledState_tally (siteB f.program) σ3 tB _ _).2.trans (oTB.2.trans hρ.tBh)
  have hGB7 : σ7.st (sGB _) = List.replicate (guardLength (input r1).length sB) true := by
    rw [(s7out _ oGB').1, s6st _ (by dst)]
    exact (calledState_guard (siteB f.program) σ3 tB _ _).1
  have hGB7h : σ7.sh (sGB _) = 0 := by
    rw [(s7out _ oGB').2, s6sh]
    exact (calledState_guard (siteB f.program) σ3 tB _ _).2.trans (oGB.2.trans hρ.gBh)
  have hL7 : σ7.st (sL _) = [] := by rw [(s7out _ oL').1]; exact hL6
  have hL7h : σ7.sh (sL _) = 0 := by rw [(s7out _ oL').2]; exact hL6h
  -- 8. erase site `B`
  obtain ⟨τ8, e8, sim8⟩ := cleanP_exec cap (siteB f.program) (guardLength (input r1).length sB) σ7
    (fun j q hq => by simp only [siteB]; rw [hB7]; exact farB j q hq) (fun j => hB7h j)
    (fun q hq => by
      simp only [siteB]; rw [hTB7]; exact readTapeBit_beyond _ _ (by simp [guardLength] at hq ⊢; omega))
    hTB7h hGB7 hGB7h (by simp only [siteB]; rw [hL7]; exact blank_nil') hL7h
    (by simp [hσ7, s6val]; exact hρ.rs 0) (by unfold guardLength; omega)
  -- the composition
  obtain ⟨τ, eτ, simτ⟩ := NearCubicGates.Close.Worker.seq_sim e1 (SimW.refl _) (NearCubicGates.Close.Worker.seq_sim e2 sim2
    (NearCubicGates.Close.Worker.seq_sim e3 (SimW.refl _) (NearCubicGates.Close.Worker.seq_sim e4 sim4 (NearCubicGates.Close.Worker.seq_sim e5 (SimW.refl _)
      (NearCubicGates.Close.Worker.seq_sim e6 (SimW.refl _) (NearCubicGates.Close.Worker.seq_sim e7 sim7 ⟨τ8, e8, sim8⟩))))))
  refine ⟨τ, eτ.mono ?_, SimW.trans ?_ simτ⟩
  · unfold roundCost writeCost callCost ltIntCost ltNatCost cleanCost guardLength
    rw [hin0, hin1]
    omega
  · -- the end state is the round state of `π ++ [bit]`
    have both : ∀ q, (siteA f.program).Out q → (siteB f.program).Out q →
        ((cleanState (siteB f.program) σ7).st q = σ6.st q ∧ (cleanState (siteB f.program) σ7).sh q = ρ.sh q) ∧
        (q ≠ sP f.program.tapeCount → σ6.st q = ρ.st q) := by
      intro q hA hB
      have hqA : q ≠ (siteA f.program).input := fun h => hA.1 _ h.symm
      have hqB : q ≠ (siteB f.program).input := fun h => hB.1 _ h.symm
      refine ⟨⟨?_, ?_⟩, fun hP => ?_⟩
      · rw [(cleanState_out _ _ q hB).1, (s7out q hA).1]
      · rw [(cleanState_out _ _ q hB).2, (s7out q hA).2, s6sh, (i4out q hB).2, s3sh, (i2out q hA).2, s1sh]
      · rw [s6st q hP, (i4out q hB).1, s3st q hqB, (i2out q hA).1, s1st q hqA hP]
    have rP : ∀ q, q ≠ sP f.program.tapeCount → (roundSt ρ (π ++ [bit])).st q = ρ.st q := fun q hq => by
      simp [roundSt, Function.update_of_ne hq]
    have oIN' : (siteB f.program).Out (sIN f.program.tapeCount) := outB _ _ (by simp)
    have oOUT : (siteA f.program).Out (sOUT f.program.tapeCount) := outA _ _ (by simp)
    have oOUT' : (siteB f.program).Out (sOUT f.program.tapeCount) := outB _ _ (by simp)
    have oTB'' : (siteA f.program).Out (sTB f.program.tapeCount) := oTB'
    have eqst : (cleanState (siteB f.program) σ7) = roundSt ρ (π ++ [bit]) := by
      refine WState.eq ?_ ?_ ?_ rfl
      · funext q
        rcases stream_cases f.program.tapeCount q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | ⟨j, rfl⟩ |
          ⟨j, rfl⟩
        · exact (both _ oIN oIN').1.2
        · exact (both _ oOUT oOUT').1.2
        · exact (both _ oP oPB).1.2
        · exact (both _ oL' oLB).1.2
        · rw [(cleanState_out _ _ _ oTA).2]
          exact (cleanState_tally (siteA f.program) σ6).2.trans (hTA6h.trans hρ.tAh.symm)
        · rw [(cleanState_out _ _ _ oGA).2]
          exact (cleanState_guard (siteA f.program) σ6).2.trans (hGA6h.trans hρ.gAh.symm)
        · exact (cleanState_tally (siteB f.program) σ7).2.trans (hTB7h.trans hρ.tBh.symm)
        · exact (cleanState_guard (siteB f.program) σ7).2.trans (hGB7h.trans hρ.gBh.symm)
        · rw [(cleanState_out _ _ _ (outB _ _ (by outs))).2]
          exact (cleanState_bank (siteA f.program) σ6 j).2.trans (hρ.bAh j).symm
        · exact (cleanState_bank (siteB f.program) σ7 j).2.trans (hρ.bBh j).symm
      · funext q
        rcases stream_cases f.program.tapeCount q with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | ⟨j, rfl⟩ |
          ⟨j, rfl⟩
        · rw [(both _ oIN oIN').1.1, (both _ oIN oIN').2 hIP, rP _ hIP]
        · have h : sOUT f.program.tapeCount ≠ sP f.program.tapeCount := by dst
          rw [(both _ oOUT oOUT').1.1, (both _ oOUT oOUT').2 h, rP _ h]
        · rw [(both _ oP oPB).1.1]; simp [hσ6, roundSt]
        · have h : sL f.program.tapeCount ≠ sP f.program.tapeCount := by dst
          rw [(both _ oL' oLB).1.1, (both _ oL' oLB).2 h, rP _ h]
        · rw [(cleanState_out _ _ _ oTA).1, rP _ (by dst), hρ.tA]
          exact (cleanState_tally (siteA f.program) σ6).1
        · rw [(cleanState_out _ _ _ oGA).1, rP _ (by dst), hρ.gA]
          exact (cleanState_guard (siteA f.program) σ6).1
        · rw [rP _ (by dst), hρ.tB]; exact (cleanState_tally (siteB f.program) σ7).1
        · rw [rP _ (by dst), hρ.gB]; exact (cleanState_guard (siteB f.program) σ7).1
        · rw [(cleanState_out _ _ _ (outB _ _ (by outs))).1, rP _ (by dst), hρ.bA]
          exact (cleanState_bank (siteA f.program) σ6 j).1
        · rw [rP _ (by dst), hρ.bB]; exact (cleanState_bank (siteB f.program) σ7 j).1
      · simp [roundSt, hσ7, s6val]
    rw [eqst]
    exact SimW.refl _

end NearQuarticWires.Control
