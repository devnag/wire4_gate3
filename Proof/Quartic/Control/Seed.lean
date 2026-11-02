import Proof.Quartic.Control.Parse
import Proof.Gates.Expand.PolyTabPack

/-!
# Measuring and rewinding the input

Paper: Step 3 of `sec:algorithm`, paper/paper.tex. Before the rounds the program reads `S` from the
word after Step 2 and must bring the head of the input back to its first cell. The skips of the call word do not
count the cells they pass, so the input is first measured.

* `walk2`, `walk2_exec`: walk over a marked word to its end, counting its cells in two registers;
* `rewindLoop_sat`: moving a head back by at least its position brings it to `0` (head moves stop at the first
  cell), so a count of the whole word rewinds the head from any position inside it.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.Control

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces (Call)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.RepairOrdinary.Streaming (marks marks_append marks_length)

variable {ns nr : ℕ}

/-- Walk over a marked word on `S`, counting its cells in `D` and in `E`. -/
def walk2 (S : Fin (ns + 1)) (D E : Fin nr) : WMX ns nr :=
  .whs S (.seq (WMX.fwd S) (.seq (WMX.fwd S) (.seq (WMX.inc D) (.seq (WMX.inc D) (.seq (WMX.inc E) (WMX.inc E))))))

theorem walk2_exec (cap : ℕ) (σ : WState ns nr) (S : Fin (ns + 1)) (D E : Fin nr) (hDE : D ≠ E) (U rest : List Bool)
    (hread : ∀ q, readTapeBit (σ.st S) q = readTapeBit (marks U ++ rest) q) (hrest : readTapeBit rest 0 = false)
    (hSh : σ.sh S = 0) (hD : σ.val D = 0) (hE : σ.val E = 0) (hc : 2 * U.length + 2 ≤ cap) :
    WXExec cap (walk2 S D E) σ (((σ.seth S (2 * U.length)).setv D (2 * U.length)).setv E (2 * U.length))
      (U.length * 26 + 1) := by
  have key : ∀ m k, k + m = U.length →
      WXExec cap (walk2 S D E) (((σ.seth S (2 * k)).setv D (2 * k)).setv E (2 * k))
        (((σ.seth S (2 * U.length)).setv D (2 * U.length)).setv E (2 * U.length)) (m * 26 + 1) := by
    intro m
    induction m with
    | zero =>
      intro k hk
      rw [Nat.add_zero] at hk; subst hk
      refine WXExec.mono (WXExec.whsF ?_) (by omega)
      simp only [wbit, WState.setv_st, WState.seth_st, WState.setv_sh, WState.seth_sh, Function.update_self, hread]
      exact read_marks_end U rest hrest
    | succ m ih =>
      intro k hk
      have hb : wbit (((σ.seth S (2 * k)).setv D (2 * k)).setv E (2 * k)) S = true := by
        simp only [wbit, WState.setv_st, WState.seth_st, WState.setv_sh, WState.seth_sh, Function.update_self, hread]
        exact read_marks_mark U rest k (by omega)
      set τ0 := ((σ.seth S (2 * k)).setv D (2 * k)).setv E (2 * k) with hτ0
      have e1 := WXExec.fwd cap S τ0
      have e2 := WXExec.fwd cap S (τ0.seth S (τ0.sh S + 1))
      set τ2 := (τ0.seth S (τ0.sh S + 1)).seth S ((τ0.seth S (τ0.sh S + 1)).sh S + 1) with hτ2
      have hD2 : τ2.val D = 2 * k := by simp [hτ2, hτ0, Function.update_of_ne hDE]
      have hE2 : τ2.val E = 2 * k := by simp [hτ2, hτ0]
      have e3 := WXExec.inc cap D τ2 (by omega)
      set τ3 := τ2.setv D (τ2.val D + 1) with hτ3
      have e4 := WXExec.inc cap D τ3 (by simp [hτ3, hD2]; omega)
      set τ4 := τ3.setv D (τ3.val D + 1) with hτ4
      have e5 := WXExec.inc cap E τ4 (by simp [hτ4, hτ3, Function.update_of_ne hDE.symm, hE2]; omega)
      set τ5 := τ4.setv E (τ4.val E + 1) with hτ5
      have e6 := WXExec.inc cap E τ5 (by simp [hτ5, hτ4, hτ3, Function.update_of_ne hDE.symm, hE2]; omega)
      have e7 := ih (k + 1) (by omega)
      have hstate : τ5.setv E (τ5.val E + 1) =
          ((σ.seth S (2 * (k + 1))).setv D (2 * (k + 1))).setv E (2 * (k + 1)) := by
        refine WState.eq ?_ rfl ?_ rfl
        · funext q; by_cases hq : q = S
          · subst hq; simp [hτ5, hτ4, hτ3, hτ2, hτ0]; omega
          · simp [hτ5, hτ4, hτ3, hτ2, hτ0, Function.update_of_ne hq]
        · funext q
          by_cases hqE : q = E
          · subst hqE; simp [hτ5, hτ4, hτ3, Function.update_of_ne hDE.symm, hE2]; omega
          · by_cases hqD : q = D
            · subst hqD; simp [hτ5, hτ4, hτ3, Function.update_of_ne hDE, hD2]; omega
            · simp [hτ5, hτ4, hτ3, hτ2, hτ0, Function.update_of_ne hqE, Function.update_of_ne hqD]
      rw [hstate] at e6
      exact WXExec.mono (WXExec.whsT hb (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4
        (WXExec.seq e5 e6))))) e7) (by ring_nf; omega)
  have h := key U.length 0 (by omega)
  have h0 : ((σ.seth S (2 * 0)).setv D (2 * 0)).setv E (2 * 0) = σ := by
    refine WState.eq ?_ rfl ?_ rfl
    · funext q; by_cases hq : q = S
      · subst hq; simp [hSh]
      · simp [Function.update_of_ne hq]
    · funext q
      by_cases hqE : q = E
      · subst hqE; simp [hE]
      · by_cases hqD : q = D
        · subst hqD; simp [Function.update_of_ne hDE, hD]
        · simp [Function.update_of_ne hqE, Function.update_of_ne hqD]
  rwa [h0] at h

/-- **A saturating rewind**: moving back by `m` cells from any position, the head stops at `0`. -/
theorem rewindLoop_sat (cap : ℕ) (S : Fin (ns + 1)) (E : Fin nr) :
    ∀ (m : ℕ) (σ : WState ns nr), σ.val E = m → m ≤ cap →
      WExec cap (NearCubicGates.Close.Codec.rewindLoop S E) σ ((σ.setv E 0).seth S (σ.sh S - m)) (5 * m + 1)
  | 0, σ, h0, _ => by
    refine WExec.cast cap (WExec.whrF h0) ?_ le_rfl
    refine WState.eq ?_ rfl ?_ rfl
    · funext q; by_cases hq : q = S
      · subst hq; simp
      · simp [Function.update_of_ne hq]
    · funext q; by_cases hq : q = E
      · subst hq; simp [h0]
      · simp [Function.update_of_ne hq]
  | m + 1, σ, hm, hc => by
    have e1 := WExec.dec (cap := cap) E σ (by omega)
    have e2 := WExec.bwd (cap := cap) S (σ.setv E (σ.val E - 1))
    have e3 := rewindLoop_sat cap S E m ((σ.setv E (σ.val E - 1)).seth S ((σ.setv E (σ.val E - 1)).sh S - 1))
      (by simp [hm]) (by omega)
    refine WExec.mono (WExec.cast cap (WExec.whrT (by omega) (WExec.seq e1 e2) e3) ?_ le_rfl) (by omega)
    refine WState.eq ?_ rfl ?_ rfl
    · funext q; by_cases hq : q = S
      · subst hq; simp; omega
      · simp [Function.update_of_ne hq]
    · funext q; by_cases hq : q = E
      · subst hq; simp
      · simp [Function.update_of_ne hq]


/-- **The prelude of a dispatched call**: measure the input, read `S` into `G 6`, rewind the input. -/
def prelude (IN : Fin (ns + 1)) (D E : Fin nr) (G : Fin 7 ↪ Fin nr) : WMX ns nr :=
  .seq (walk2 IN D E) (.seq (.wm (NearCubicGates.Close.Codec.rewindLoop IN D))
    (.seq (.wm (readS IN G)) (.wm (NearCubicGates.Close.Codec.rewindLoop IN E))))

/-- The cost of the prelude on a word of length `w`. -/
def preludeCost (w r : ℕ) : ℕ := 50 * (w + 1) + r + 10

/-- **The prelude.** On `frame` of `true :: callWord c ++ natWords xs ++ natWord S ++ rest` (head `0`), with the
registers `D`, `E` and `G` at zero, the prelude puts `S` in `G 6` and changes nothing else. -/
theorem prelude_exec (cap : ℕ) (σ : WState ns nr) (IN : Fin (ns + 1)) (D E : Fin nr) (G : Fin 7 ↪ Fin nr)
    (hDE : D ≠ E) (hDG : ∀ i, G i ≠ D) (hEG : ∀ i, G i ≠ E) (c : Call) (xs : List ℕ) (S : ℕ) (rest : List Bool)
    (hIN : σ.st IN = frame ([true] ++ NearCubicGates.Close.Interfaces.callWord c ++ xs.flatMap natWord ++
      natWord S ++ rest))
    (hINh : σ.sh IN = 0) (hD : σ.val D = 0) (hE : σ.val E = 0) (hz : ∀ i, σ.val (G i) = 0)
    (hfit : ReadFits cap c xs S) (hxs : xs.length = 19)
    (hc : 2 * ([true] ++ NearCubicGates.Close.Interfaces.callWord c ++ xs.flatMap natWord ++ natWord S ++
      rest).length + 2 ≤ cap) :
    WXExec cap (prelude IN D E G) σ (σ.setv (G 6) S)
      (preludeCost ([true] ++ NearCubicGates.Close.Interfaces.callWord c ++ xs.flatMap natWord ++ natWord S ++
        rest).length (readCost c xs S)) := by
  set W := [true] ++ NearCubicGates.Close.Interfaces.callWord c ++ xs.flatMap natWord ++ natWord S ++ rest with hW
  have hIN' : σ.st IN = marks W ++ [false] := by rw [hIN, NearCubicGates.Close.Codec.frame_eq_marks]
  have e1 := walk2_exec cap σ IN D E hDE W [false] (fun q => by rw [hIN']) rfl hINh hD hE hc
  set σ1 := ((σ.seth IN (2 * W.length)).setv D (2 * W.length)).setv E (2 * W.length) with hσ1
  have e2 := NearCubicGates.Close.Codec.rewindLoop_spec cap IN D (2 * W.length) σ1
    (by simp [hσ1, Function.update_of_ne hDE]) (by simp [hσ1]) (by omega)
  set σ2 := (σ1.setv D 0).seth IN (σ1.sh IN - 2 * W.length) with hσ2
  have h2 : σ2 = (σ.setv E (2 * W.length)) := by
    refine WState.eq ?_ rfl ?_ rfl
    · funext q; by_cases hq : q = IN
      · subst hq; simp [hσ2, hσ1, hINh]
      · simp [hσ2, hσ1, Function.update_of_ne hq]
    · funext q
      by_cases hqD : q = D
      · subst hqD; simp [hσ2, hσ1, Function.update_of_ne hDE, hD]
      · by_cases hqE : q = E
        · subst hqE; simp [hσ2, hσ1, Function.update_of_ne hqD]
        · simp [hσ2, hσ1, Function.update_of_ne hqD, Function.update_of_ne hqE]
  rw [h2] at e2
  have e3 := readS_exec cap (σ.setv E (2 * W.length)) IN G c xs S rest [false]
    (by show σ.st IN = _; rw [hIN']) (by simp [hINh]) (fun i => by simp [Function.update_of_ne (hEG i), hz i])
    hfit hxs
  have hp3W : (marks ([true] ++ NearCubicGates.Close.Interfaces.callWord c ++ xs.flatMap natWord ++
      natWord S)).length ≤ 2 * W.length := by
    have hW' : W = ([true] ++ NearCubicGates.Close.Interfaces.callWord c ++ xs.flatMap natWord ++ natWord S) ++
        rest := by rw [hW]
    rw [hW', List.length_append, marks_length]; omega
  have e4 := rewindLoop_sat cap IN E (2 * W.length) (((σ.setv E (2 * W.length)).seth IN
    (marks ([true] ++ NearCubicGates.Close.Interfaces.callWord c ++ xs.flatMap natWord ++ natWord S)).length).setv
      (G 6) S)
    (by simp [Function.update_of_ne (hEG 6).symm]) (by omega)
  refine WXExec.mono (WXExec.cast cap (WXExec.seq e1 (WXExec.seq (WXExec.wm e2) (WXExec.seq (WXExec.wm e3)
    (WXExec.wm e4)))) ?_ le_rfl) ?_
  · refine WState.eq ?_ rfl ?_ rfl
    · funext q; by_cases hq : q = IN
      · subst hq; simp only [WState.seth_sh, WState.setv_sh, Function.update_self]; rw [hINh]; omega
      · simp [Function.update_of_ne hq]
    · funext q
      by_cases hqE : q = E
      · subst hqE; simp [Function.update_of_ne (hEG 6).symm, hE]
      · by_cases hq6 : q = G 6
        · subst hq6; simp [Function.update_of_ne hqE]
        · simp [Function.update_of_ne hqE, Function.update_of_ne hq6]
  · unfold preludeCost; omega


/-! ## The program of Step 3 -/

/-- The counters of the measurement of the input. -/
def rD : Fin lnr := ⟨12, by simp only [lnr]; omega⟩
/-- The second counter of the measurement of the input. -/
def rE : Fin lnr := ⟨13, by simp only [lnr]; omega⟩
/-- The registers of the reading of `S`; the last one is the round counter `K`. -/
def rR : Fin 7 ↪ Fin lnr :=
  ⟨fun i => if i.val = 6 then rK else ⟨14 + i.val, by simp only [lnr]; omega⟩, by
    intro a b h
    have ha := a.isLt; have hb := b.isLt
    by_cases h6a : a.val = 6 <;> by_cases h6b : b.val = 6 <;> simp only [h6a, h6b, if_true, if_false] at h
    · exact Fin.ext (by omega)
    · have := congrArg Fin.val h; simp [rK] at this; omega
    · have := congrArg Fin.val h; simp [rK] at this; omega
    · have := congrArg Fin.val h; simp at this; exact Fin.ext this⟩

theorem rR_six : rR 6 = rK := by simp [rR]

/-- **The program of Step 3** for the child program `p`: on the tag `1` of a dispatched call, read `S`, run the `S`
rounds and write the word after Step 3; on the tag `0`, copy the word. -/
noncomputable def seedP (p : Program) : WMX (lns p.tapeCount) lnr :=
  .seq (WMX.fwd (sIN _))
    (.ifs (sIN _)
      (.seq (WMX.bwd (sIN _)) (.seq (prelude (sIN _) rD rE rR) (.seq (roundsP p) (writeSeed (sIN _) (sP _) (sOUT _) rOP rC))))
      (.seq (WMX.bwd (sIN _)) (writeCopy (sIN _) (sOUT _) rOP rC)))

/-- The cost bound of the program of Step 3 on a dispatched call. -/
def seedCost (w S r B : ℕ) : ℕ := preludeCost w r + S * (roundCost w S B + 4) + writeOutCost w S + 20


/-- The start of the program (`Expand.PolyTab.idealStart`): `frame w` on the input stream, every other stream empty,
every head and register at `0`. -/
abbrev seedStart (t : ℕ) (w : List Bool) : WState (lns t) lnr :=
  NearCubicGates.Close.Expand.PolyTab.idealStart (lns t) lnr w (fun _ => 0)

theorem seedStart_st (t : ℕ) (w : List Bool) (q : Fin (lns t + 1)) :
    (seedStart t w).st q = if q.val = 0 then frame w else [] := by
  simp [NearCubicGates.Close.Expand.PolyTab.idealStart]

theorem seedStart_ready (t : ℕ) (w : List Bool) : LoopReady t (seedStart t w) w where
  inp := by rw [seedStart_st]; simp
  inph := rfl
  ph := rfl
  ruler := by rw [seedStart_st]; simp
  rulerh := rfl
  bA := fun j => by rw [seedStart_st]; simp [bankA]
  bAh := fun _ => rfl
  bB := fun j => by rw [seedStart_st]; simp [bankB]
  bBh := fun _ => rfl
  tA := by rw [seedStart_st]; simp
  tAh := rfl
  gA := by rw [seedStart_st]; simp
  gAh := rfl
  tB := by rw [seedStart_st]; simp
  tBh := rfl
  gB := by rw [seedStart_st]; simp
  gBh := rfl
  rs := fun _ => rfl
  rg := fun _ => rfl
  op := rfl
  c := rfl

theorem roundsP_avoids (p : Program) : WMX.Avoids (sOUT p.tapeCount) (roundsP p) :=
  ⟨trivial, roundP_avoids p⟩

/-- **Step 3 on a dispatched call.** From the start on `w = true :: callWord c ++ natWords xs ++ natWord S ++ rest`,
with a child word function `f` whose requests `req π` have the input `w ++ frame π`, the value `R π` and a budget at
most `B`, the program writes exactly `frame (w ++ bitWord true ++ frame (greedyLoop S R))` on the output stream. -/
theorem seedP_dispatched {Request : Type} {input : Request → List Bool} {Rv : Request → ℤ} {budget : Request → ℕ}
    (f : WordFunction Request input (fun r => NearCubicGates.Close.Interfaces.intWord (Rv r)) budget)
    (cap : ℕ) (w : List Bool) (c : Call) (xs : List ℕ) (S : ℕ) (rest : List Bool)
    (hw : w = [true] ++ NearCubicGates.Close.Interfaces.callWord c ++ xs.flatMap natWord ++ natWord S ++ rest)
    (hxs : xs.length = 19) (hfit : ReadFits cap c xs S) (R : List Bool → ℤ)
    (req : (π : List Bool) → π.length ≤ S → Request)
    (hreq : ∀ π h, input (req π h) = w ++ frame π ∧ Rv (req π h) = R π) (B : ℕ)
    (hB : ∀ π h, budget (req π h) ≤ B) (hcap : 10 * (w.length + S + B + 10) ≤ cap) :
    ∃ τ, WXExec cap (seedP f.program) (seedStart _ w) τ (seedCost w.length S (readCost c xs S) B) ∧
      τ.st (sOUT _) = frame (w ++ NearCubicGates.Close.Interfaces.bitWord true ++
        frame (NearCubicWires.WireExponent3_5.SeedFix.greedyLoop S R)) := by
  set σ0 := seedStart f.program.tapeCount w with hσ0
  have hIN0 : σ0.st (sIN _) = frame w := by rw [hσ0, seedStart_st]; simp
  -- the tag
  have e1 := WXExec.fwd cap (sIN f.program.tapeCount) σ0
  have hb : wbit (σ0.seth (sIN _) (σ0.sh (sIN _) + 1)) (sIN _) = true := by
    simp only [wbit, WState.seth_st, WState.seth_sh, Function.update_self, hIN0]
    rw [hw]; simp [hσ0, NearCubicGates.Close.Expand.PolyTab.idealStart, frame, readTapeBit]
  have e2 := WXExec.bwd cap (sIN f.program.tapeCount) (σ0.seth (sIN _) (σ0.sh (sIN _) + 1))
  have h2 : (σ0.seth (sIN _) (σ0.sh (sIN _) + 1)).seth (sIN _)
      ((σ0.seth (sIN _) (σ0.sh (sIN _) + 1)).sh (sIN _) - 1) = σ0 := by
    refine WState.eq ?_ rfl rfl rfl
    funext q; by_cases hq : q = sIN _
    · subst hq; simp [hσ0, NearCubicGates.Close.Expand.PolyTab.idealStart]
    · simp [Function.update_of_ne hq]
  rw [h2] at e2
  -- `S`
  have hDE : rD ≠ rE := by decide
  have hDG : ∀ i, rR i ≠ rD := fun i => by
    intro h; have := congrArg Fin.val h; simp only [rR, Function.Embedding.coeFn_mk] at this
    split_ifs at this <;> simp [rK, rD] at this; omega
  have hEG : ∀ i, rR i ≠ rE := fun i => by
    intro h; have := congrArg Fin.val h; simp only [rR, Function.Embedding.coeFn_mk] at this
    split_ifs at this <;> simp [rK, rE] at this; omega
  have e3 := prelude_exec cap σ0 (sIN _) rD rE rR hDE hDG hEG c xs S rest (by rw [hIN0, hw]) rfl rfl rfl
    (fun _ => rfl) hfit hxs (by rw [← hw]; omega)
  rw [rR_six] at e3
  -- the rounds
  have hready := seedStart_ready f.program.tapeCount w
  have hσS : roundSt (σ0.setv rK S) [] = σ0.setv rK S := by
    unfold roundSt; exact BinW.sets_same (by rw [WState.setv_st, hσ0, seedStart_st]; simp [marks])
  obtain ⟨τ1, e4, sim4⟩ := rounds_exec f cap σ0 w hready S R req hreq B hB hcap (σ0.setv rK S)
    (by rw [hσS]; exact NearCubicWires.WireExponent3_5.PrimT.ReadEq.SimW.refl _)
  have hOUT := WXExec.avoids e4 (roundsP_avoids f.program)
  -- the output
  have hseed : (NearCubicWires.WireExponent3_5.SeedFix.greedyLoop S R).length = S := greedy_iterate_length R S
  have hIP : sIN f.program.tapeCount ≠ sP _ := ne_of_val _ (by simp)
  have hIO : sIN f.program.tapeCount ≠ sOUT _ := ne_of_val _ (by simp)
  have hPO : sP f.program.tapeCount ≠ sOUT _ := ne_of_val _ (by simp)
  have hsh1 : τ1.sh (sIN f.program.tapeCount) = 0 := by rw [sim4.sh]; rfl
  have hshP : τ1.sh (sP f.program.tapeCount) = 0 := by rw [sim4.sh]; rfl
  have hst1 : ∀ q, readTapeBit (σ0.st (sIN _)) q = readTapeBit (τ1.st (sIN f.program.tapeCount)) q := by
    intro q
    have := sim4.st (sIN _) q
    simpa [roundSt, Function.update_of_ne hIP] using this
  have hstP : ∀ q, readTapeBit (marks (NearCubicWires.WireExponent3_5.SeedFix.greedyLoop S R)) q =
      readTapeBit (τ1.st (sP f.program.tapeCount)) q := by
    intro q
    have := sim4.st (sP _) q
    simpa [roundSt] using this
  obtain ⟨τ2, e5, hout⟩ := writeSeed_exec cap τ1 (sIN _) (sP _) (sOUT _) rOP rC hIP hIO hPO (by decide) w
    (NearCubicWires.WireExponent3_5.SeedFix.greedyLoop S R)
    (fun q => by rw [hsh1, Nat.zero_add, ← hst1 q, hIN0, NearCubicGates.Close.Codec.frame_eq_marks])
    (fun q => by rw [hshP, Nat.zero_add, ← hstP q, List.append_nil])
    (by rw [hOUT.1]; simp [hσ0, seedStart_st]) (by rw [hOUT.2]; rfl) (by rw [sim4.val]; rfl) (by rw [sim4.val]; rfl)
    (by rw [hseed]; omega)
  rw [hseed] at e5
  rw [← hw] at e3
  refine ⟨τ2, WXExec.mono (WXExec.seq e1 (WXExec.ifsT hb (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 e5))))) ?_,
    hout⟩
  unfold seedCost
  omega


/-- **Step 3 on any other call.** From the start on a word `w` whose tag is `0`, the program copies `frame w` to the
output stream. -/
theorem seedP_copy (p : Program) (cap : ℕ) (w rest : List Bool) (hw : w = false :: rest)
    (hcap : 6 * w.length + 6 ≤ cap) :
    ∃ τ, WXExec cap (seedP p) (seedStart _ w) τ (writeOutCost w.length 0 + 6) ∧ τ.st (sOUT _) = frame w := by
  set σ0 := seedStart p.tapeCount w with hσ0
  have hIN0 : σ0.st (sIN _) = frame w := by rw [hσ0, seedStart_st]; simp
  have e1 := WXExec.fwd cap (sIN p.tapeCount) σ0
  have hb : wbit (σ0.seth (sIN _) (σ0.sh (sIN _) + 1)) (sIN _) = false := by
    simp only [wbit, WState.seth_st, WState.seth_sh, Function.update_self, hIN0]
    rw [hw]; simp [hσ0, NearCubicGates.Close.Expand.PolyTab.idealStart, frame, readTapeBit]
  have e2 := WXExec.bwd cap (sIN p.tapeCount) (σ0.seth (sIN _) (σ0.sh (sIN _) + 1))
  have h2 : (σ0.seth (sIN _) (σ0.sh (sIN _) + 1)).seth (sIN _)
      ((σ0.seth (sIN _) (σ0.sh (sIN _) + 1)).sh (sIN _) - 1) = σ0 := by
    refine WState.eq ?_ rfl rfl rfl
    funext q; by_cases hq : q = sIN _
    · subst hq; simp [hσ0, NearCubicGates.Close.Expand.PolyTab.idealStart]
    · simp [Function.update_of_ne hq]
  rw [h2] at e2
  have hIO : sIN p.tapeCount ≠ sOUT _ := ne_of_val _ (by simp)
  obtain ⟨τ, e3, hout⟩ := writeCopy_exec cap σ0 (sIN _) (sOUT _) rOP rC hIO (by decide) w
    (fun q => by rw [show σ0.sh (sIN _) = 0 from rfl, Nat.zero_add, hIN0, NearCubicGates.Close.Codec.frame_eq_marks])
    (by rw [hσ0, seedStart_st]; simp) rfl rfl rfl hcap
  exact ⟨τ, WXExec.mono (WXExec.seq e1 (WXExec.ifsF hb (WXExec.seq e2 e3))) (by omega), hout⟩

end NearQuarticWires.Control
