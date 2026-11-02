import Proof.Quartic.Control.Request

/-!
# One walk of the coefficient stage

Paper: Step 3 of `sec:algorithm`, paper/paper.tex, `cor:conditional`, and `prop:time`: the coefficient stage of a child evaluation computes `2^S c_π(w)` for every closed walk `w`.

The program works on one layout (`cIN` … `cGA`, the bank of the coefficient program): the input, the output, the
fixed part of the requests (`cHS`), the walk index as count fields (`cCT`), the table (`cT`), the ruler, and one
call site. One walk (`walkBody`): write the request of the current walk (`writeRequest`), call the coefficient
program (`callP`), append its value to the table (`appendGamma`), erase the bank (`cleanP`), and move to the next
walk (`incWalk`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.Control

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.RepairOrdinary.Streaming (marks marks_length marks_append)

section Layout

variable (t : ℕ)

/-- The number of streams minus one of the coefficient stage: eight named streams and a bank of `t` tapes. -/
abbrev cns : ℕ := 7 + t

/-- The input. -/
def cIN : Fin (cns t + 1) := ⟨0, by simp only [cns]; omega⟩
/-- The output. -/
def cOUT : Fin (cns t + 1) := ⟨1, by simp only [cns]; omega⟩
/-- The fixed part of the requests. -/
def cHS : Fin (cns t + 1) := ⟨2, by simp only [cns]; omega⟩
/-- The walk index. -/
def cCT : Fin (cns t + 1) := ⟨3, by simp only [cns]; omega⟩
/-- The table. -/
def cT : Fin (cns t + 1) := ⟨4, by simp only [cns]; omega⟩
/-- The ruler. -/
def cL : Fin (cns t + 1) := ⟨5, by simp only [cns]; omega⟩
/-- The tally of the call site. -/
def cTA : Fin (cns t + 1) := ⟨6, by simp only [cns]; omega⟩
/-- The guard of the call site. -/
def cGA : Fin (cns t + 1) := ⟨7, by simp only [cns]; omega⟩
/-- The bank of the coefficient program. -/
def cbank (j : Fin t) : Fin (cns t + 1) := ⟨8 + j.val, by simp only [cns]; omega⟩

theorem cbank_inj : Function.Injective (cbank t) := fun a b h => Fin.ext (by
  have := congrArg Fin.val h; simp [cbank] at this; omega)

theorem cne {a b : Fin (cns t + 1)} (h : a.val ≠ b.val) : a ≠ b := fun e => h (congrArg Fin.val e)

end Layout

/-- The output counter of the writers. -/
def cOP : Fin lnr := ⟨4, by simp only [lnr]; omega⟩
/-- The read counter of the writers. -/
def cC : Fin lnr := ⟨5, by simp only [lnr]; omega⟩
/-- The bound on the length of the walk index. -/
def cLC : Fin lnr := ⟨6, by simp only [lnr]; omega⟩
/-- A scratch register. -/
def cD : Fin lnr := ⟨7, by simp only [lnr]; omega⟩
/-- The registers of the number transcoder. -/
def cY : Fin 5 ↪ Fin lnr :=
  ⟨fun i => ⟨8 + i.val, by simp only [lnr]; omega⟩, fun a b h => Fin.ext (by have := congrArg Fin.val h; simp at this; omega)⟩
/-- The registers of the copy of a coefficient. -/
def cR : Fin 8 ↪ Fin lnr :=
  ⟨fun i => ⟨13 + i.val, by simp only [lnr]; omega⟩, fun a b h => Fin.ext (by have := congrArg Fin.val h; simp at this; omega)⟩
/-- The registers of the increment of the walk index. -/
def cZ : Fin 5 ↪ Fin lnr :=
  ⟨fun i => ⟨21 + i.val, by simp only [lnr]; omega⟩, fun a b h => Fin.ext (by have := congrArg Fin.val h; simp at this; omega)⟩

/-- **The call site** of the coefficient program `p`. -/
def siteC (p : Program) : Site p (cns p.tapeCount) lnr where
  bank := cbank p.tapeCount
  tally := cTA p.tapeCount
  guard := cGA p.tapeCount
  ruler := cL p.tapeCount
  regs := rS
  bank_inj := cbank_inj _
  tally_ne := fun j => cne _ (by simp [cbank, cTA]; omega)
  guard_ne := fun j => cne _ (by simp [cbank, cGA]; omega)
  ruler_ne := fun j => cne _ (by simp [cbank, cL]; omega)
  tally_guard := cne _ (by simp [cTA, cGA])
  tally_ruler := cne _ (by simp [cTA, cL])
  guard_ruler := cne _ (by simp [cGA, cL])

/-- **One walk** of the coefficient stage for the coefficient program `p`. -/
noncomputable def walkBody (p : Program) : WMX (cns p.tapeCount) lnr :=
  .seq (writeRequest 8 (cHS _) (cCT _) (siteC p).input cOP cC cLC cD cY)
  (.seq (callP (siteC p))
  (.seq (.wm (appendGamma (cbank _ p.outputTape) (cT _) cR))
  (.seq (cleanP (siteC p))
  (incWalk 8 (cCT _) cZ cLC cC cD))))


theorem outC (p : Program) (q : Fin (cns p.tapeCount + 1)) (h : q.val < 6) : (siteC p).Out q := by
  refine ⟨fun j hj => ?_, fun hj => ?_, fun hj => ?_⟩
  · have := congrArg Fin.val hj; simp [siteC, cbank] at this; omega
  · have := congrArg Fin.val hj; simp [siteC, cTA] at this; omega
  · have := congrArg Fin.val hj; simp [siteC, cGA] at this; omega

/-- The state of the coefficient stage, apart from the walk index and the table. -/
structure CoeffReady (t : ℕ) (ρ : WState (cns t) lnr) (hw : List Bool) (kh Lc : ℕ) : Prop where
  hs : ρ.st (cHS t) = marks hw ++ [false]
  hsh : ρ.sh (cHS t) = 0
  cth : ρ.sh (cCT t) = 0
  ruler : ρ.st (cL t) = []
  rulerh : ρ.sh (cL t) = 0
  b : ∀ j, ρ.st (cbank t j) = []
  bh : ∀ j, ρ.sh (cbank t j) = 0
  ta : ρ.st (cTA t) = []
  tah : ρ.sh (cTA t) = 0
  ga : ρ.st (cGA t) = []
  gah : ρ.sh (cGA t) = 0
  rs : ∀ i, ρ.val (rS i) = 0
  op : ρ.val cOP = 0
  c : ρ.val cC = 0
  d : ρ.val cD = 0
  lc : ρ.val cLC = Lc
  y : ∀ i, ρ.val (cY i) = 0
  r : ∀ i, ρ.val (cR i) = 0
  z0 : ρ.val (cZ 0) = 0
  z1 : ρ.val (cZ 1) = 0
  z2 : ρ.val (cZ 2) = 0
  z3 : ρ.val (cZ 3) = kh
  z4 : ρ.val (cZ 4) = 0

/-- The state before a walk: the count fields of the digits `ds` on the walk index, the table `Tw` with its head at
its end. -/
def coeffSt {t : ℕ} (ρ : WState (cns t) lnr) (kh : ℕ) (ds : List ℕ) (Tw : List Bool) : WState (cns t) lnr :=
  ((ρ.sets (cCT t) (ds.flatMap (countField kh))).sets (cT t) Tw).seth (cT t) Tw.length


/-- Every stream of the coefficient layout is a named stream or a tape of the bank. -/
theorem streamC_cases (t : ℕ) (q : Fin (cns t + 1)) :
    q.val < 8 ∨ ∃ j, q = cbank t j := by
  by_cases h : q.val < 8
  · exact Or.inl h
  · right
    have := q.isLt; simp only [cns] at this
    exact ⟨⟨q.val - 8, by omega⟩, Fin.ext (by simp [cbank]; omega)⟩

/-- Two streams of the coefficient layout differ (by their indices). -/
local macro "cdst" : tactic =>
  `(tactic| (apply cne; simp [Site.input, siteC, cbank, NearCubicGates.Close.WorkerArith.inTape, cIN, cOUT, cHS,
    cCT, cT, cL, cTA, cGA] <;> omega))

/-- Two registers of the coefficient layout differ (by their indices). -/
local macro "rdst" : tactic =>
  `(tactic| (intro hh; have hv := congrArg Fin.val hh; simp [cY, cR, cZ, cOP, cC, cLC, cD, rS] at hv <;> omega))

/-- The cost bound of one walk. -/
def walkCost (h kh Lc w B : ℕ) : ℕ :=
  requestCost h 8 kh Lc + callCost w B + (130 * (B + 1) + 2) + cleanCost (2 * w + 2 + B) +
    (5 + 4 * 8 + (8 * (60 * kh + 25) + 1) + 18 * Lc + 3 + 5 * Lc + 1 + 4) + 4

/-- **One walk.** From the state before a walk with the digits `ds` (`8` count fields) and the table `Tw`, with a
coefficient word function `f` whose request `r` has the input `hw ++ natWord 8 ++ natWords ds` and a budget at most
`B`, the walk reaches a state that reads like the state before the next walk: the digits `digitsInc ds 1`, the
table `Tw ++ marks (intWord (R r))`, the carry out in `cZ 0`. -/
theorem walkBody_exec {Request : Type} {input : Request → List Bool} {Rv : Request → ℤ} {budget : Request → ℕ}
    (f : WordFunction Request input (fun r => NearCubicGates.Close.Interfaces.intWord (Rv r)) budget)
    (cap : ℕ) (ρ : WState (cns f.program.tapeCount) lnr) (hw : List Bool) (kh Lc : ℕ)
    (hρ : CoeffReady f.program.tapeCount ρ hw kh Lc) (ds : List ℕ) (hds : ∀ d ∈ ds, d < 2 ^ kh)
    (hlen : ds.length = 8) (Tw : List Bool) (r : Request)
    (hin : input r = hw ++ natWord 8 ++ ds.flatMap natWord) (B : ℕ) (hB : budget r ≤ B)
    (hLc : 8 * (2 * kh + 1) ≤ Lc)
    (hcap : 10 * (hw.length + 8 * kh + Lc + B + 50) + 8 * 8 + 10 * (8 + 2) * (4 * kh + 8) ≤ cap) :
    ∃ τ, WXExec cap (walkBody f.program) (coeffSt ρ kh ds Tw) τ
        (walkCost hw.length kh Lc (input r).length B) ∧
      NearCubicWires.WireExponent3_5.PrimT.ReadEq.SimW
        ((coeffSt ρ kh (digitsInc kh ds true).1 (Tw ++ marks (NearCubicGates.Close.Interfaces.intWord (Rv r)))).setv
          (cZ 0) (digitsInc kh ds true).2.toNat) τ := by
  have ht2 := f.program.twoTapes
  have hlenin : (input r).length = hw.length + (natWord 8).length + (ds.flatMap natWord).length := by
    rw [hin]; simp only [List.length_append]
  have hsl : (ds.flatMap natWord).length ≤ ds.length * (2 * kh + 3) := by
    have := sum_map_le ds (fun d => (natWord d).length) (fun _ => 2 * kh + 3)
      (fun d hd => natWord_length_le_field kh d (hds d hd))
    rw [List.length_flatMap]; simpa using this
  have hn8 : (natWord 8).length = 9 := by decide
  -- distinct streams
  have hHX : cHS f.program.tapeCount ≠ (siteC f.program).input := by cdst
  have hCX : cCT f.program.tapeCount ≠ (siteC f.program).input := by cdst
  have hHC : cHS f.program.tapeCount ≠ cCT _ := by cdst
  have hTX : cT f.program.tapeCount ≠ (siteC f.program).input := by cdst
  -- the state before the walk
  set σ0 := coeffSt ρ kh ds Tw with hσ0
  have s0st : ∀ q, q ≠ cCT f.program.tapeCount → q ≠ cT _ → σ0.st q = ρ.st q := fun q h1 h2 => by
    simp [hσ0, coeffSt, Function.update_of_ne h1, Function.update_of_ne h2]
  have s0sh : ∀ q, q ≠ cT f.program.tapeCount → σ0.sh q = ρ.sh q := fun q h => by
    simp [hσ0, coeffSt, Function.update_of_ne h]
  have s0val : σ0.val = ρ.val := rfl
  -- 1. the request
  have e1 := writeRequest_exec cap σ0 8 (cHS _) (cCT _) (siteC f.program).input cOP cC cLC cD cY hHX hCX hHC
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (fun i => by rdst) (fun i => by rdst)
    hw ds kh Lc hds hlen (by rw [s0st _ hHC (by cdst)]; exact hρ.hs) (by rw [s0sh _ (by cdst)]; exact hρ.hsh)
    (by simp [hσ0, coeffSt, Function.update_of_ne (show cCT f.program.tapeCount ≠ cT _ by cdst)])
    (by rw [s0sh _ (by cdst)]; exact hρ.cth)
    (by rw [s0st _ (by cdst) (by cdst)]; exact hρ.b _) (by rw [s0sh _ (by cdst)]; exact hρ.bh _)
    hρ.op hρ.c hρ.lc hρ.d hρ.y hLc (by nlinarith)
  rw [show hw ++ natWord 8 ++ ds.flatMap natWord = input r from hin.symm] at e1
  set σ1 := σ0.sets (siteC f.program).input (frame (input r)) with hσ1
  have s1st : ∀ q, q ≠ (siteC f.program).input → σ1.st q = σ0.st q := fun q h => by
    simp [hσ1, Function.update_of_ne h]
  have s1sh : σ1.sh = σ0.sh := rfl
  have s1val : σ1.val = ρ.val := rfl
  -- 2. the call
  have hin2 : ∀ j, σ1.st ((siteC f.program).bank j) = f.program.inputTapes (input r) j := by
    intro j
    by_cases hj : j = NearCubicGates.Close.WorkerArith.inTape f.program
    · subst hj
      simp only [hσ1, WState.sets_st, Site.input, Function.update_self]
      simp [Program.inputTapes, NearCubicGates.Close.WorkerArith.inTape]
    · have hne : (siteC f.program).bank j ≠ (siteC f.program).input :=
        fun h => hj ((siteC f.program).bank_inj h)
      rw [s1st _ hne, s0st _ (by cdst) (by cdst)]
      have hv : ¬ (j.val = 0) := fun h => hj (Fin.ext h)
      simp only [siteC, hρ.b, Program.inputTapes]
      rw [if_neg hv]
  obtain ⟨tA, sA, τ2, houtA, hsA, hlenA, farA, e2, sim2⟩ := callP_exec f r cap (siteC f.program) σ1 hin2
    (fun j => by rw [s1sh, s0sh _ (by cdst)]; exact hρ.bh j)
    (by rw [s1st _ (by cdst), s0st _ (by cdst) (by cdst)]; exact hρ.ta)
    (by rw [s1sh, s0sh _ (by cdst)]; exact hρ.tah)
    (by rw [s1st _ (by cdst), s0st _ (by cdst) (by cdst)]; exact hρ.ga)
    (by rw [s1sh, s0sh _ (by cdst)]; exact hρ.gah)
    (by rw [s1st _ (by cdst), s0st _ (by cdst) (by cdst)]; simp only [siteC, hρ.ruler]; exact blank_nil')
    (by rw [s1sh, s0sh _ (by cdst)]; exact hρ.rulerh) (fun i => by rw [s1val]; exact hρ.rs i)
    (by rw [hlenin]; nlinarith)
  set ι2 := calledState (siteC f.program) σ1 tA (input r).length sA with hι2
  have i2out : ∀ q, (siteC f.program).Out q → ι2.st q = σ1.st q ∧ ι2.sh q = σ1.sh q :=
    fun q hq => calledState_out _ _ _ _ _ q hq
  have i2val : ι2.val = ρ.val := rfl
  -- 3. the coefficient into the table
  have oT : (siteC f.program).Out (cT f.program.tapeCount) := outC _ _ (by simp [cT])
  have hO2 : ι2.st (cbank _ f.program.outputTape) = NearCubicGates.Close.Interfaces.intWord (Rv r) ++ [] := by
    rw [List.append_nil, ← houtA]; exact (calledState_bank (siteC f.program) σ1 tA _ _ _).1
  have hO2h : ι2.sh (cbank _ f.program.outputTape) = 0 := (calledState_bank (siteC f.program) σ1 tA _ _ _).2
  have hT2 : ι2.st (cT _) = Tw := by
    rw [(i2out _ oT).1, s1st _ hTX]; simp [hσ0, coeffSt]
  have hT2h : ι2.sh (cT _) = Tw.length := by
    rw [(i2out _ oT).2, s1sh]; simp [hσ0, coeffSt]
  have hLa : (NearCubicGates.Close.Interfaces.intWord (Rv r)).length ≤ B + 1 := by rw [← houtA]; omega
  have e3 := appendGamma_exec cap ι2 (cbank _ f.program.outputTape) (cT _) (by cdst) cR (Rv r) [] hO2 hO2h
    (by rw [hT2, hT2h]) (by rw [i2val]; exact hρ.r 1) (by rw [i2val]; exact hρ.r 2) (by rw [i2val]; exact hρ.r 7)
    (by nlinarith)
  set σ3 := (NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO ι2 (cT _) (cR 7)
    (marks (NearCubicGates.Close.Interfaces.intWord (Rv r)))).setv (cR 7) 0 with hσ3
  have s3st : ∀ q, q ≠ cT f.program.tapeCount → σ3.st q = ι2.st q := fun q h => by
    simp [hσ3, Function.update_of_ne h]
  have s3sh : ∀ q, q ≠ cT f.program.tapeCount → σ3.sh q = ι2.sh q := fun q h => by
    simp [hσ3, Function.update_of_ne h]
  -- 4. erase the bank
  have hbt : ∀ j, (siteC f.program).bank j ≠ cT f.program.tapeCount := fun j => by cdst
  obtain ⟨τ4, e4, sim4⟩ := cleanP_exec cap (siteC f.program) (guardLength (input r).length sA) σ3
    (fun j q hq => by rw [s3st _ (hbt j), (calledState_bank (siteC f.program) σ1 tA _ _ _).1]; exact farA j q hq)
    (fun j => by rw [s3sh _ (hbt j)]; exact (calledState_bank (siteC f.program) σ1 tA _ _ _).2)
    (fun q hq => by
      rw [s3st _ (by cdst)]
      show readTapeBit ((calledState (siteC f.program) σ1 tA (input r).length sA).st (siteC f.program).tally) q = false
      rw [(calledState_tally (siteC f.program) σ1 tA _ _).1]
      exact NearCubicGates.Close.CheckedPCPP.readTapeBit_beyond _ _ (by simp [guardLength] at hq ⊢; omega))
    (by
      rw [s3sh _ (by cdst)]
      show (calledState (siteC f.program) σ1 tA (input r).length sA).sh (siteC f.program).tally = 0
      rw [(calledState_tally (siteC f.program) σ1 tA _ _).2, s1sh, s0sh _ (by cdst)]; exact hρ.tah)
    (by
      rw [s3st _ (by cdst)]
      exact (calledState_guard (siteC f.program) σ1 tA _ _).1)
    (by
      rw [s3sh _ (by cdst)]
      show (calledState (siteC f.program) σ1 tA (input r).length sA).sh (siteC f.program).guard = 0
      rw [(calledState_guard (siteC f.program) σ1 tA _ _).2, s1sh, s0sh _ (by cdst)]; exact hρ.gah)
    (by
      rw [s3st _ (by cdst)]
      show NearCubicGates.Close.Worker.Blank (ι2.st (cL _))
      rw [(i2out _ (outC _ _ (by simp [cL]))).1, s1st _ (by cdst), s0st _ (by cdst) (by cdst), hρ.ruler]
      exact blank_nil')
    (by
      rw [s3sh _ (by cdst)]
      show ι2.sh (cL _) = 0
      rw [(i2out _ (outC _ _ (by simp [cL]))).2, s1sh, s0sh _ (by cdst)]; exact hρ.rulerh)
    (by
      show σ3.val (rS 0) = 0
      simp [hσ3, Function.update_of_ne (show rS 0 ≠ cR 7 by decide), i2val, hρ.rs 0])
    (by unfold guardLength; nlinarith)
  set ι4 := cleanState (siteC f.program) σ3 with hι4
  have i4out : ∀ q, (siteC f.program).Out q → ι4.st q = σ3.st q ∧ ι4.sh q = σ3.sh q :=
    fun q hq => cleanState_out _ _ q hq
  -- 5. the next walk
  have oCT : (siteC f.program).Out (cCT f.program.tapeCount) := outC _ _ (by simp [cCT])
  have hCT4 : ι4.st (cCT _) = ds.flatMap (countField kh) ++ [] := by
    rw [(i4out _ oCT).1, s3st _ (by cdst), (i2out _ oCT).1, s1st _ (by cdst)]
    simp [hσ0, coeffSt, Function.update_of_ne (show cCT f.program.tapeCount ≠ cT _ by cdst)]
  have hCT4h : ι4.sh (cCT _) = 0 := by
    rw [(i4out _ oCT).2, s3sh _ (by cdst), (i2out _ oCT).2, s1sh, s0sh _ (by cdst)]; exact hρ.cth
  have v4 : ∀ q, q ≠ cR 7 → ι4.val q = ρ.val q := fun q hq => by
    simp [hι4, hσ3, Function.update_of_ne hq, i2val]
  have e5 := incWalk_exec cap ι4 (cCT _) cZ cLC cC cD (fun i => by rdst) (fun i => by rdst) (fun i => by rdst)
    (by decide) (by decide) (by decide) kh Lc ds hds [] hCT4 hCT4h
    (by rw [v4 _ (by rdst)]; exact hρ.z0) (by rw [v4 _ (by rdst)]; exact hρ.z1) (by rw [v4 _ (by rdst)]; exact hρ.z2)
    (by rw [v4 _ (by rdst)]; exact hρ.z3) (by rw [v4 _ (by rdst)]; exact hρ.z4) (by rw [v4 _ (by decide)]; exact hρ.c)
    (by rw [v4 _ (by decide)]; exact hρ.d) (by rw [v4 _ (by decide)]; exact hρ.lc) (by rw [hlen]; exact hLc)
    (by rw [hlen]; nlinarith)
  rw [hlen] at e5
  obtain ⟨τ, eτ, simτ⟩ := NearCubicGates.Close.Worker.seq_sim e1
    (NearCubicWires.WireExponent3_5.PrimT.ReadEq.SimW.refl _)
    (NearCubicGates.Close.Worker.seq_sim e2 sim2 (NearCubicGates.Close.Worker.seq_sim (WXExec.wm e3)
      (NearCubicWires.WireExponent3_5.PrimT.ReadEq.SimW.refl _) (NearCubicGates.Close.Worker.seq_sim e4 sim4
        ⟨_, e5, NearCubicWires.WireExponent3_5.PrimT.ReadEq.SimW.refl _⟩)))
  refine ⟨τ, eτ.mono ?_, NearCubicGates.Close.CheckedPCPP.SimW.trans ?_ simτ⟩
  · unfold walkCost callCost cleanCost guardLength
    omega
  · -- the end state is the state before the next walk
    have heq : ι4.sets (cCT _) ((digitsInc kh ds true).1.flatMap (countField kh) ++ []) =
        coeffSt ρ kh (digitsInc kh ds true).1 (Tw ++ marks (NearCubicGates.Close.Interfaces.intWord (Rv r))) := by
      have hplain : ∀ q : Fin (cns f.program.tapeCount + 1), q.val < 8 → q ≠ cTA _ → q ≠ cGA _ →
          (siteC f.program).Out q := fun q h8 h6 h7 => outC _ _ (by
            have a6 : q.val ≠ 6 := fun e => h6 (Fin.ext (by simp [cTA, e]))
            have a7 : q.val ≠ 7 := fun e => h7 (Fin.ext (by simp [cGA, e]))
            omega)
      have chainSt : ∀ q : Fin (cns f.program.tapeCount + 1), q.val < 8 → q ≠ cTA _ → q ≠ cGA _ →
          q ≠ cCT _ → q ≠ cT _ → ι4.st q = ρ.st q := by
        intro q h8 h6 h7 hC hT
        have hO := hplain q h8 h6 h7
        have hX : q ≠ (siteC f.program).input := fun e => hO.1 _ e.symm
        rw [(i4out q hO).1, s3st q hT, (i2out q hO).1, s1st q hX, s0st q hC hT]
      have chainSh : ∀ q : Fin (cns f.program.tapeCount + 1), q.val < 8 → q ≠ cTA _ → q ≠ cGA _ →
          q ≠ cT _ → ι4.sh q = ρ.sh q := by
        intro q h8 h6 h7 hT
        have hO := hplain q h8 h6 h7
        rw [(i4out q hO).2, s3sh q hT, (i2out q hO).2, s1sh, s0sh q hT]
      have hTA4 : ι4.st (cTA _) = [] ∧ ι4.sh (cTA _) = ρ.sh (cTA _) := by
        refine ⟨(cleanState_tally (siteC f.program) σ3).1, ?_⟩
        show (cleanState (siteC f.program) σ3).sh (siteC f.program).tally = _
        rw [(cleanState_tally (siteC f.program) σ3).2]
        show σ3.sh (cTA _) = _
        rw [s3sh _ (by cdst)]
        show (calledState (siteC f.program) σ1 tA (input r).length sA).sh (siteC f.program).tally = _
        rw [(calledState_tally (siteC f.program) σ1 tA _ _).2, s1sh, s0sh _ (by cdst)]; rfl
      have hGA4 : ι4.st (cGA _) = [] ∧ ι4.sh (cGA _) = ρ.sh (cGA _) := by
        refine ⟨(cleanState_guard (siteC f.program) σ3).1, ?_⟩
        show (cleanState (siteC f.program) σ3).sh (siteC f.program).guard = _
        rw [(cleanState_guard (siteC f.program) σ3).2]
        show σ3.sh (cGA _) = _
        rw [s3sh _ (by cdst)]
        show (calledState (siteC f.program) σ1 tA (input r).length sA).sh (siteC f.program).guard = _
        rw [(calledState_guard (siteC f.program) σ1 tA _ _).2, s1sh, s0sh _ (by cdst)]; rfl
      have hT4 : ι4.st (cT _) = Tw ++ marks (NearCubicGates.Close.Interfaces.intWord (Rv r)) ∧
          ι4.sh (cT _) = (Tw ++ marks (NearCubicGates.Close.Interfaces.intWord (Rv r))).length := by
        rw [(i4out _ oT).1, (i4out _ oT).2]
        simp [hσ3, hT2, hT2h]
      refine WState.eq ?_ ?_ ?_ rfl
      · funext q
        simp only [WState.sets_sh]
        rcases streamC_cases _ q with h8 | ⟨j, rfl⟩
        · by_cases hT : q = cT _
          · rw [hT, hT4.2]; simp [coeffSt]
          · have hRHS : (coeffSt ρ kh (digitsInc kh ds true).1
                (Tw ++ marks (NearCubicGates.Close.Interfaces.intWord (Rv r)))).sh q = ρ.sh q := by
              simp [coeffSt, Function.update_of_ne hT]
            rw [hRHS]
            by_cases h6 : q = cTA _
            · rw [h6, hTA4.2]
            · by_cases h7 : q = cGA _
              · rw [h7, hGA4.2]
              · exact chainSh q h8 h6 h7 hT
        · have hRHS : (coeffSt ρ kh (digitsInc kh ds true).1
              (Tw ++ marks (NearCubicGates.Close.Interfaces.intWord (Rv r)))).sh (cbank _ j) = ρ.sh (cbank _ j) := by
            simp [coeffSt, Function.update_of_ne (show cbank f.program.tapeCount j ≠ cT _ by cdst)]
          rw [hRHS, hρ.bh]
          exact (cleanState_bank (siteC f.program) σ3 j).2
      · funext q
        by_cases hC : q = cCT _
        · rw [hC]; simp [coeffSt, Function.update_of_ne (show cCT f.program.tapeCount ≠ cT _ by cdst)]
        · simp only [WState.sets_st, Function.update_of_ne hC]
          rcases streamC_cases _ q with h8 | ⟨j, rfl⟩
          · by_cases hT : q = cT _
            · rw [hT, hT4.1]; simp [coeffSt]
            · have hRHS : (coeffSt ρ kh (digitsInc kh ds true).1
                  (Tw ++ marks (NearCubicGates.Close.Interfaces.intWord (Rv r)))).st q = ρ.st q := by
                simp [coeffSt, Function.update_of_ne hT, Function.update_of_ne hC]
              rw [hRHS]
              by_cases h6 : q = cTA _
              · rw [h6, hTA4.1, hρ.ta]
              · by_cases h7 : q = cGA _
                · rw [h7, hGA4.1, hρ.ga]
                · exact chainSt q h8 h6 h7 hC hT
          · have hRHS : (coeffSt ρ kh (digitsInc kh ds true).1
                (Tw ++ marks (NearCubicGates.Close.Interfaces.intWord (Rv r)))).st (cbank _ j) = ρ.st (cbank _ j) := by
              simp [coeffSt, Function.update_of_ne (show cbank f.program.tapeCount j ≠ cT _ by cdst),
                Function.update_of_ne (show cbank f.program.tapeCount j ≠ cCT _ by cdst)]
            rw [hRHS, hρ.b]
            exact (cleanState_bank (siteC f.program) σ3 j).1
      · funext q
        simp only [WState.sets_val, coeffSt, WState.seth_val]
        show σ3.val q = ρ.val q
        by_cases hq : q = cR 7
        · rw [hq]; simp [hσ3, hρ.r 7]
        · simp [hσ3, Function.update_of_ne hq, i2val]

    rw [heq]
    exact NearCubicWires.WireExponent3_5.PrimT.ReadEq.SimW.refl _


/-! ## All the walks -/

/-- The flag "more walks". -/
def cNX : Fin lnr := ⟨26, by simp only [lnr]; omega⟩

/-- After a walk: on a carry out of the walk index, clear the flag and the carry. -/
def flagStep {t : ℕ} : WMX (cns t) lnr := .ifr (cZ 0) (.seq (WMX.dec cNX) (WMX.dec (cZ 0))) WMX.skip

/-- **All the walks**: while the flag is set, one walk and the flag step. -/
noncomputable def walksP (p : Program) : WMX (cns p.tapeCount) lnr := .whr cNX (.seq (walkBody p) flagStep)

/-- The table after the first `i` walks: the marked coefficients, in order. -/
def tableMarks (γ : ℕ → ℤ) (i : ℕ) : List Bool :=
  (List.range i).flatMap fun j => marks (NearCubicGates.Close.Interfaces.intWord (γ j))

theorem tableMarks_succ (γ : ℕ → ℤ) (i : ℕ) :
    tableMarks γ (i + 1) = tableMarks γ i ++ marks (NearCubicGates.Close.Interfaces.intWord (γ i)) := by
  simp [tableMarks, List.range_succ]

theorem coeffReady_setv {t : ℕ} {ρ : WState (cns t) lnr} {hw : List Bool} {kh Lc : ℕ}
    (h : CoeffReady t ρ hw kh Lc) (v : ℕ) : CoeffReady t (ρ.setv cNX v) hw kh Lc where
  hs := h.hs
  hsh := h.hsh
  cth := h.cth
  ruler := h.ruler
  rulerh := h.rulerh
  b := h.b
  bh := h.bh
  ta := h.ta
  tah := h.tah
  ga := h.ga
  gah := h.gah
  rs := fun i => by
    have : rS i ≠ cNX := by intro hh; have hv := congrArg Fin.val hh; simp [rS, cNX] at hv; omega
    simp [Function.update_of_ne this, h.rs i]
  op := by simp [Function.update_of_ne (show cOP ≠ cNX by decide), h.op]
  c := by simp [Function.update_of_ne (show cC ≠ cNX by decide), h.c]
  d := by simp [Function.update_of_ne (show cD ≠ cNX by decide), h.d]
  lc := by simp [Function.update_of_ne (show cLC ≠ cNX by decide), h.lc]
  y := fun i => by
    have : cY i ≠ cNX := by intro hh; have hv := congrArg Fin.val hh; simp [cY, cNX] at hv; omega
    simp [Function.update_of_ne this, h.y i]
  r := fun i => by
    have : cR i ≠ cNX := by intro hh; have hv := congrArg Fin.val hh; simp [cR, cNX] at hv; omega
    simp [Function.update_of_ne this, h.r i]
  z0 := by simp [Function.update_of_ne (show cZ 0 ≠ cNX by decide), h.z0]
  z1 := by simp [Function.update_of_ne (show cZ 1 ≠ cNX by decide), h.z1]
  z2 := by simp [Function.update_of_ne (show cZ 2 ≠ cNX by decide), h.z2]
  z3 := by simp [Function.update_of_ne (show cZ 3 ≠ cNX by decide), h.z3]
  z4 := by simp [Function.update_of_ne (show cZ 4 ≠ cNX by decide), h.z4]


theorem coeffSt_setv {t : ℕ} (ρ : WState (cns t) lnr) (kh : ℕ) (ds : List ℕ) (Tw : List Bool) (q : Fin lnr) (v : ℕ) :
    (coeffSt ρ kh ds Tw).setv q v = coeffSt (ρ.setv q v) kh ds Tw := rfl

theorem setv_setv' {ns nr : ℕ} (σ : WState ns nr) (r : Fin nr) (a b : ℕ) : (σ.setv r a).setv r b = σ.setv r b := by
  refine WState.eq rfl rfl ?_ rfl
  funext q; by_cases hq : q = r
  · subst hq; simp
  · simp [Function.update_of_ne hq]

theorem setv_comm {ns nr : ℕ} (σ : WState ns nr) (r s : Fin nr) (h : r ≠ s) (a b : ℕ) :
    (σ.setv r a).setv s b = (σ.setv s b).setv r a := by
  refine WState.eq rfl rfl ?_ rfl
  funext q
  by_cases hq : q = r
  · subst hq; simp [Function.update_of_ne h]
  · by_cases hq' : q = s
    · subst hq'; simp [Function.update_of_ne (Ne.symm h)]
    · simp [Function.update_of_ne hq, Function.update_of_ne hq']

/-- The flag step without a carry: nothing changes. -/
theorem flagStep_zero (cap : ℕ) {t : ℕ} (σ : WState (cns t) lnr) (h0 : σ.val (cZ 0) = 0) :
    WXExec cap (flagStep (t := t)) σ σ 1 :=
  WXExec.mono (WXExec.ifrF h0 (WXExec.skip cap σ)) le_rfl

/-- The flag step after the last walk: the flag and the carry are cleared. -/
theorem flagStep_one (cap : ℕ) {t : ℕ} (σ : WState (cns t) lnr) (h0 : σ.val (cZ 0) = 1) (hN : σ.val cNX = 1)
    (hc : 1 ≤ cap) : WXExec cap (flagStep (t := t)) σ ((σ.setv cNX 0).setv (cZ 0) 0) 4 := by
  have e1 := WXExec.dec cap cNX σ (by omega)
  rw [hN] at e1
  have e2 := WXExec.dec cap (cZ 0) (σ.setv cNX (1 - 1)) (by
    simp [Function.update_of_ne (show cZ 0 ≠ cNX by decide), h0]; omega)
  have hv : (σ.setv cNX (1 - 1)).val (cZ 0) - 1 = 0 := by
    simp [Function.update_of_ne (show cZ 0 ≠ cNX by decide), h0]
  rw [hv] at e2
  exact WXExec.mono (WXExec.ifrT (by omega) (WXExec.seq e1 e2)) le_rfl

/-- **All the walks.** From the state of walk `0` with the flag set, with a coefficient word function whose request
`req i` for the walk of index `i` has the input `hw ++ natWord 8 ++ natWords (digits of i)` and a budget at most
`B`, the walks run `2^{8kh}` times and reach the state with the table of all the coefficients and the flag
cleared. -/
theorem walks_exec {Request : Type} {input : Request → List Bool} {Rv : Request → ℤ} {budget : Request → ℕ}
    (f : WordFunction Request input (fun r => NearCubicGates.Close.Interfaces.intWord (Rv r)) budget)
    (cap : ℕ) (ρ : WState (cns f.program.tapeCount) lnr) (hw : List Bool) (kh Lc : ℕ)
    (hρ : CoeffReady f.program.tapeCount ρ hw kh Lc) (req : ℕ → Request)
    (hin : ∀ i, input (req i) = hw ++ natWord 8 ++ (walkDigits kh 8 i).flatMap natWord) (B Win : ℕ)
    (hB : ∀ i, budget (req i) ≤ B) (hWin : ∀ i, (input (req i)).length ≤ Win) (hLc : 8 * (2 * kh + 1) ≤ Lc)
    (hcap : 10 * (hw.length + 8 * kh + Lc + B + 50) + 8 * 8 + 10 * (8 + 2) * (4 * kh + 8) ≤ cap)
    (Tw : List Bool) (σ : WState (cns f.program.tapeCount) lnr)
    (hσ : NearCubicWires.WireExponent3_5.PrimT.ReadEq.SimW (coeffSt (ρ.setv cNX 1) kh (walkDigits kh 8 0) Tw) σ) :
    ∃ τ, WXExec cap (walksP f.program) σ τ (2 ^ (kh * 8) * (walkCost hw.length kh Lc Win B + 7) + 1) ∧
      NearCubicWires.WireExponent3_5.PrimT.ReadEq.SimW
        (coeffSt (ρ.setv cNX 0) kh (walkDigits kh 8 (2 ^ (kh * 8))) (Tw ++ tableMarks (fun i => Rv (req i))
          (2 ^ (kh * 8)))) τ := by
  set N8 := 2 ^ (kh * 8) with hN8
  have hpos : 0 < N8 := by positivity
  have hcostw : ∀ i, walkCost hw.length kh Lc (input (req i)).length B ≤ walkCost hw.length kh Lc Win B := by
    intro i; have := hWin i; unfold walkCost callCost cleanCost; omega
  have hz0 : ρ.val (cZ 0) = 0 := hρ.z0
  obtain ⟨τ, e, hτ⟩ := Runs.whr (cap := cap) (r := cNX) (P := .seq (walkBody f.program) flagStep)
    (fun k τ => (k = 0 ∧ NearCubicWires.WireExponent3_5.PrimT.ReadEq.SimW
        (coeffSt (ρ.setv cNX 0) kh (walkDigits kh 8 N8) (Tw ++ tableMarks (fun i => Rv (req i)) N8)) τ) ∨
      (1 ≤ k ∧ k ≤ N8 ∧ NearCubicWires.WireExponent3_5.PrimT.ReadEq.SimW
        (coeffSt (ρ.setv cNX 1) kh (walkDigits kh 8 (N8 - k)) (Tw ++ tableMarks (fun i => Rv (req i)) (N8 - k))) τ))
    (walkCost hw.length kh Lc Win B + 5) (fun τ => NearCubicWires.WireExponent3_5.PrimT.ReadEq.SimW
        (coeffSt (ρ.setv cNX 0) kh (walkDigits kh 8 N8) (Tw ++ tableMarks (fun i => Rv (req i)) N8)) τ)
    (by
      rintro τ (⟨-, hs⟩ | ⟨h1, -⟩)
      · refine ⟨?_, hs⟩
        rw [hs.val]; simp [coeffSt]
      · omega)
    (by
      rintro k τ (⟨h0, -⟩ | ⟨-, hk, hs⟩)
      · omega
      have hiN : N8 - (k + 1) < N8 := by omega
      refine ⟨by rw [hs.val]; simp [coeffSt], ?_⟩
      have hds := walkDigits_lt kh 8 (N8 - (k + 1))
      obtain ⟨τ0, e0, s0⟩ := walkBody_exec f cap (ρ.setv cNX 1) hw kh Lc (coeffReady_setv hρ 1)
        (walkDigits kh 8 (N8 - (k + 1))) hds (walkDigits_length kh 8 _)
        (Tw ++ tableMarks (fun i => Rv (req i)) (N8 - (k + 1))) (req (N8 - (k + 1))) (hin _) B (hB _) hLc hcap
      obtain ⟨τ1, e1, s1⟩ := NearCubicGates.Close.CheckedPCPP.wxexec_sim e0 τ hs
      rw [digitsInc_walkDigits kh 8 (N8 - (k + 1)) hiN, coeffSt_setv, List.append_assoc, ← tableMarks_succ] at s0
      have hS := NearCubicGates.Close.CheckedPCPP.SimW.trans s0 s1
      have hcw := hcostw (N8 - (k + 1))
      by_cases hlast : k = 0
      · -- the last walk: the carry clears the flag
        subst hlast
        have hc1 : decide (N8 - (0 + 1) + 1 = N8) = true := by simp; omega
        rw [hc1] at hS
        have ef := flagStep_one cap (coeffSt ((ρ.setv cNX 1).setv (cZ 0) (true : Bool).toNat) kh
          (walkDigits kh 8 (N8 - (0 + 1) + 1)) (Tw ++ tableMarks (fun i => Rv (req i)) (N8 - (0 + 1) + 1)))
          (by simp [coeffSt]) (by simp [coeffSt, Function.update_of_ne (show cNX ≠ cZ 0 by decide)]) (by omega)
        obtain ⟨τ2, e2, s2⟩ := NearCubicGates.Close.CheckedPCPP.wxexec_sim ef τ1 hS
        refine ⟨τ2, WXExec.mono (WXExec.seq e1 e2) (by omega), Or.inl ⟨rfl, ?_⟩⟩
        have hN : N8 - (0 + 1) + 1 = N8 := by omega
        rw [hN] at s2
        have heq : ((coeffSt ((ρ.setv cNX 1).setv (cZ 0) (true : Bool).toNat) kh (walkDigits kh 8 N8)
            (Tw ++ tableMarks (fun i => Rv (req i)) N8)).setv cNX 0).setv (cZ 0) 0 =
            coeffSt (ρ.setv cNX 0) kh (walkDigits kh 8 N8) (Tw ++ tableMarks (fun i => Rv (req i)) N8) := by
          rw [coeffSt_setv, coeffSt_setv]
          congr 1
          refine WState.eq rfl rfl ?_ rfl
          funext q
          by_cases hq : q = cZ 0
          · subst hq; simp [Function.update_of_ne (show cZ 0 ≠ cNX by decide), hz0]
          · by_cases hq' : q = cNX
            · subst hq'; simp [Function.update_of_ne hq]
            · simp [Function.update_of_ne hq, Function.update_of_ne hq']
        rw [heq] at s2
        exact s2
      · -- not the last walk: no carry
        have hc0 : decide (N8 - (k + 1) + 1 = N8) = false := by simp; omega
        rw [hc0] at hS
        have hσeq : (ρ.setv cNX 1).setv (cZ 0) (false : Bool).toNat = ρ.setv cNX 1 :=
          BinW.setv_same (by simp [Function.update_of_ne (show cZ 0 ≠ cNX by decide), hz0])
        rw [hσeq] at hS
        have ef := flagStep_zero cap τ1 (by rw [hS.val]; simp [coeffSt, Function.update_of_ne
          (show cZ 0 ≠ cNX by decide), hz0])
        refine ⟨τ1, WXExec.mono (WXExec.seq e1 ef) (by omega), Or.inr ⟨by omega, by omega, ?_⟩⟩
        have hN : N8 - (k + 1) + 1 = N8 - k := by omega
        rw [hN] at hS
        exact hS)
    N8 σ (Or.inr ⟨by omega, le_rfl, by rw [Nat.sub_self]; simpa [tableMarks] using hσ⟩)
  exact ⟨τ, WXExec.mono e (by ring_nf; omega), hτ⟩

end NearQuarticWires.Control
