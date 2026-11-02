import Proof.Quartic.Control.Prefix

/-!
# The state before the first walk

Paper: Step 3 of `sec:algorithm`, paper/paper.tex, and `prop:time`: the coefficient table lists
the `N^{2m} = 2^{8 kh}` coefficients after their number (`Greedy.gammaTableWord`), and the walks are counted from
the walk index `0`.

* `tableStart`, `tableStart_exec`: two zero cells (the stop of `sentinelRewind`), then
  `marks (natWord 2^{8 kh})` (`natWord_two_pow`) on the table;
* `indexStart`, `indexStart_exec`: eight count fields of the digit `0` (`countField_zero`) on the walk index;
* `walkStart`, `walkStart_exec`: both, the bound `16 kh + 8` on the length of the index, the fixed part of the
  requests rewound, the flag of the walk loop set.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearQuarticWires.Control

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.RepairOrdinary.Streaming (marks marks_length marks_append)
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat (appendO appendO_st appendO_sh appendO_val appendO_cell
  appendO_append appendO_setv emitPair emitPair_spec)

/-- Two registers of the prelude differ (by their indices). -/
local macro "pdst" : tactic =>
  `(tactic| (intro hh; have hv := congrArg Fin.val hh; simp [cY, cR, cZ, cG, cOP, cC, cLC, cD, cNX, rS, rO, rI, rH,
    rT] at hv <;> omega))

variable {ns nr : ℕ} (cap : ℕ)

/-! ## Repetitions -/

/-- `n` times `C := C + Q`. -/
def dupsR (Q C D : Fin nr) : ℕ → WM ns nr
  | 0 => .skip
  | n + 1 => .seq (NearCubicGates.Close.Codec.dupR Q C D) (dupsR Q C D n)

theorem dupsR_exec (Q C D : Fin nr) (hQC : Q ≠ C) (hQD : Q ≠ D) (hCD : C ≠ D) :
    ∀ (n : ℕ) (σ : WState ns nr), σ.val D = 0 → σ.val C + n * σ.val Q ≤ cap →
      WExec cap (dupsR Q C D n) σ (σ.setv C (σ.val C + n * σ.val Q)) (n * (18 * σ.val Q + 4))
  | 0, σ, _, _ => by
    refine WExec.cast cap (WExec.skip σ) ?_ (by simp)
    simp [wsetv_same]
  | n + 1, σ, hD, hc => by
    have e1 := NearCubicGates.Close.Codec.dupR_spec cap Q C D hQC hQD hCD σ hD (by nlinarith)
    have e2 := dupsR_exec Q C D hQC hQD hCD n (σ.setv C (σ.val C + σ.val Q))
      (by simp [Function.update_of_ne hCD.symm, hD]) (by simp [Function.update_of_ne hQC]; nlinarith)
    refine WExec.cast cap (WExec.seq e1 e2) ?_ (by simp [Function.update_of_ne hQC]; ring_nf; omega)
    rw [wsetv_setv]; simp [Function.update_of_ne hQC]; ring_nf

/-- `n` times `P`. -/
def repeatP (P : WM ns nr) : ℕ → WM ns nr
  | 0 => .skip
  | n + 1 => .seq P (repeatP P n)

/-- **Repetition of an append** under an invariant. -/
theorem repeatP_exec (o : Fin (ns + 1)) (OP : Fin nr) (P : WM ns nr) (w : List Bool) (c s : ℕ)
    (Pre : WState ns nr → Prop) (hPre : ∀ σ, Pre σ → Pre (appendO σ o OP w))
    (hP : ∀ σ, Pre σ → σ.sh o = (σ.st o).length → σ.val OP + w.length + s ≤ cap →
      WExec cap P σ (appendO σ o OP w) c) :
    ∀ (n : ℕ) (σ : WState ns nr), Pre σ → σ.sh o = (σ.st o).length → σ.val OP + n * w.length + s ≤ cap →
      WExec cap (repeatP P n) σ (appendO σ o OP (List.replicate n w).flatten) (n * (c + 1))
  | 0, σ, _, _, _ => by
    refine WExec.cast cap (WExec.skip σ) ?_ (by simp)
    simp [NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO_nil]
  | n + 1, σ, hp, ho, hc => by
    have e1 := hP σ hp ho (by nlinarith)
    have e2 := repeatP_exec o OP P w c s Pre hPre hP n (appendO σ o OP w) (hPre σ hp) (by simp [ho])
      (by simp; nlinarith)
    refine WExec.cast cap (WExec.seq e1 e2) ?_ (by ring_nf; omega)
    rw [appendO_append, List.replicate_succ, List.flatten_cons]

/-- `kh` times `P`, for `kh` in `cZ 3` (kept). -/
def runKh {ns : ℕ} (P : WM ns lnr) : WM ns lnr :=
  .seq (NearCubicGates.Close.Codec.dupR (cZ 3) (cR 1) cD) (runLoop (cR 1) P)

theorem runKh_exec {ns : ℕ} (o : Fin (ns + 1)) (OP : Fin lnr) (hO : OP ≠ cR 1) (P : WM ns lnr) (u : List Bool)
    (c : ℕ) (hP : ∀ σ : WState ns lnr, σ.sh o = (σ.st o).length → σ.val OP + u.length ≤ cap →
      WExec cap P σ (appendO σ o OP u) c)
    (σ : WState ns lnr) (kh : ℕ) (hZ : σ.val (cZ 3) = kh) (h1 : σ.val (cR 1) = 0) (hD : σ.val cD = 0)
    (ho : σ.sh o = (σ.st o).length) (hc : σ.val OP + kh * u.length + kh ≤ cap) :
    WExec cap (runKh P) σ (appendO σ o OP (List.replicate kh u).flatten) (18 * kh + 3 + 1 + (kh * (c + 4) + 1)) := by
  have e1 := NearCubicGates.Close.Codec.dupR_spec cap (cZ 3) (cR 1) cD (by pdst) (by pdst) (by pdst) σ hD
    (by rw [hZ, h1]; omega)
  rw [h1, hZ, Nat.zero_add] at e1
  have e2 := runLoop_exec cap (cR 1) OP o hO.symm P u c hP kh (σ.setv (cR 1) kh) (by simp) (by simpa using ho)
    (by simp [Function.update_of_ne hO]; nlinarith) (by omega)
  refine WExec.cast cap (WExec.seq e1 e2) ?_ le_rfl
  have hs : σ.setv (cR 1) 0 = σ := by rw [← h1, wsetv_same]
  rw [appendO_setv _ _ _ _ hO.symm, wsetv_setv, ← appendO_setv _ _ _ _ hO.symm, hs]

theorem flatten_replicate_single (n : ℕ) (b : Bool) : (List.replicate n [b]).flatten = List.replicate n b := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

theorem flatten_replicate_pair (n : ℕ) (b : Bool) :
    (List.replicate n [true, b]).flatten = marks (List.replicate n b) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih, marks]

/-! ## The walk index -/

/-- One count field of the digit `0` on `CT`. -/
def zeroField {ns : ℕ} (CT : Fin (ns + 1)) (OP : Fin lnr) : WM ns lnr :=
  .seq (runKh (emitC CT OP true)) (.seq (emitC CT OP false) (runKh (emitC CT OP false)))

theorem zeroField_exec {ns : ℕ} (CT : Fin (ns + 1)) (OP : Fin lnr) (hO : OP ≠ cR 1) (hOZ : OP ≠ cZ 3)
    (hOD : OP ≠ cD) (σ : WState ns lnr) (kh : ℕ) (hZ : σ.val (cZ 3) = kh) (h1 : σ.val (cR 1) = 0)
    (hD : σ.val cD = 0) (ho : σ.sh CT = (σ.st CT).length) (hc : σ.val OP + (countField kh 0).length + 2 * kh ≤ cap) :
    WExec cap (zeroField CT OP) σ (appendO σ CT OP (countField kh 0)) (60 * kh + 30) := by
  have hcl : (countField kh 0).length = 2 * kh + 1 := by simp [countField_zero]; ring
  have hP : ∀ b : Bool, ∀ τ : WState ns lnr, τ.sh CT = (τ.st CT).length → τ.val OP + [b].length ≤ cap →
      WExec cap (emitC CT OP b) τ (appendO τ CT OP [b]) 7 :=
    fun b τ h1 h2 => emitC_app cap CT OP b τ h1 (by simp at h2; omega)
  have e1 := runKh_exec cap CT OP hO (emitC CT OP true) [true] 7 (hP true) σ kh hZ h1 hD ho (by simp; omega)
  set σ1 := appendO σ CT OP (List.replicate kh [true]).flatten with hσ1
  have e2 := emitC_app cap CT OP false σ1 (by simp [hσ1, ho]) (by simp [hσ1, flatten_replicate_single]; omega)
  set σ2 := appendO σ1 CT OP [false] with hσ2
  have h2OP : σ2.val OP = σ.val OP + kh + 1 := by
    simp only [hσ2, hσ1, appendO_val, Function.update_self, flatten_replicate_single, List.length_replicate,
      List.length_singleton]
  have h2o : σ2.sh CT = (σ2.st CT).length := by
    simp only [hσ2, hσ1, appendO_sh, appendO_st, Function.update_self, flatten_replicate_single,
      List.length_replicate, List.length_singleton, List.length_append, ho]
  have e3 := runKh_exec cap CT OP hO (emitC CT OP false) [false] 7 (hP false) σ2 kh
    (by simp [hσ2, hσ1, Function.update_of_ne hOZ.symm, hZ]) (by simp [hσ2, hσ1, Function.update_of_ne hO.symm, h1])
    (by simp [hσ2, hσ1, Function.update_of_ne hOD.symm, hD]) h2o
    (by rw [h2OP]; simp only [List.length_singleton]; omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 e3)) ?_ (by omega)
  rw [hσ2, hσ1, appendO_append, appendO_append, countField_zero, flatten_replicate_single,
    flatten_replicate_single]
  simp

theorem walkDigits_zero (kh : ℕ) : ∀ m, walkDigits kh m 0 = List.replicate m 0
  | 0 => rfl
  | m + 1 => by simp [walkDigits, walkDigits_zero kh m, List.replicate_succ]

theorem fields_zero (kh : ℕ) :
    (List.replicate 8 (countField kh 0)).flatten = (walkDigits kh 8 0).flatMap (countField kh) := by
  rw [walkDigits_zero]; simp [List.flatMap_replicate]


/-! ## The table -/

/-- Two zero cells, then `marks (natWord 2^{8 kh})`. -/
def tableStart {ns : ℕ} (T : Fin (ns + 1)) : WM ns lnr :=
  .seq (emitC T rT false) (.seq (emitC T rT false)
  (.seq (dupsR (cZ 3) (cR 1) cD 8)
  (.seq (emitPair T rT true)
  (.seq (runLoop (cR 1) (emitPair T rT true))
  (.seq (emitPair T rT false)
  (.seq (dupsR (cZ 3) (cR 1) cD 8)
  (.seq (runLoop (cR 1) (emitPair T rT false))
  (emitPair T rT true))))))))

/-- The start of the table: two zero cells, then the number of walks. -/
def tableHead (kh : ℕ) : List Bool := [false, false] ++ marks (natWord (2 ^ (8 * kh)))

theorem tableHead_eq (kh : ℕ) : tableHead kh = [false] ++ [false] ++ [true, true] ++
    (List.replicate (8 * kh) [true, true]).flatten ++ [true, false] ++ (List.replicate (8 * kh) [true, false]).flatten ++
      [true, true] := by
  rw [tableHead, natWord_two_pow, flatten_replicate_pair, flatten_replicate_pair]
  simp [marks_append, List.replicate_succ, marks]

theorem tableHead_length (kh : ℕ) : (tableHead kh).length = 32 * kh + 8 := by
  rw [tableHead_eq]; simp; ring

/-- The cost of `tableStart`. -/
def tableCost (kh : ℕ) : ℕ :=
  7 + 1 + (7 + 1 + (8 * (18 * kh + 4) + 1 + (15 + 1 + (8 * kh * (15 + 4) + 1 + 1 + (15 + 1 + (8 * (18 * kh + 4) + 1 +
    (8 * kh * (15 + 4) + 1 + 1 + 15)))))))

theorem tableStart_exec {ns : ℕ} (T : Fin (ns + 1)) (σ : WState ns lnr) (kh : ℕ) (hZ : σ.val (cZ 3) = kh)
    (h1 : σ.val (cR 1) = 0) (hD : σ.val cD = 0) (ho : σ.sh T = (σ.st T).length)
    (hc : σ.val rT + 40 * kh + 20 ≤ cap) :
    WExec cap (tableStart T) σ (appendO σ T rT (tableHead kh)) (tableCost kh) := by
  have hr1 : rT ≠ cR 1 := by pdst
  have hrZ : rT ≠ cZ 3 := by pdst
  have hrD : rT ≠ cD := by pdst
  have hP : ∀ b : Bool, ∀ τ : WState ns lnr, τ.sh T = (τ.st T).length → τ.val rT + [true, b].length ≤ cap →
      WExec cap (emitPair T rT b) τ (appendO τ T rT [true, b]) 15 :=
    fun b τ h1 h2 => emitPair_spec cap T rT b τ h1 (by simpa using h2)
  have e1 := emitC_app cap T rT false σ ho (by omega)
  set σ1 := appendO σ T rT [false] with hσ1
  have e2 := emitC_app cap T rT false σ1 (by simp [hσ1, ho]) (by simp [hσ1]; omega)
  set σ2 := appendO σ1 T rT [false] with hσ2
  have e3 := dupsR_exec cap (cZ 3) (cR 1) cD (by pdst) (by pdst) (by pdst) 8 σ2
    (by simp [hσ2, hσ1, Function.update_of_ne hrD.symm, hD])
    (by simp [hσ2, hσ1, Function.update_of_ne hrZ.symm, Function.update_of_ne hr1.symm, hZ, h1]; omega)
  have h2Z : σ2.val (cZ 3) = kh := by simp [hσ2, hσ1, Function.update_of_ne hrZ.symm, hZ]
  have h2R : σ2.val (cR 1) = 0 := by simp [hσ2, hσ1, Function.update_of_ne hr1.symm, h1]
  rw [h2Z, h2R, Nat.zero_add] at e3
  set σ3 := σ2.setv (cR 1) (8 * kh) with hσ3
  have e4 := emitPair_spec cap T rT true σ3 (by simp [hσ3, hσ2, hσ1, ho])
    (by simp [hσ3, hσ2, hσ1, Function.update_of_ne hr1]; omega)
  set σ4 := appendO σ3 T rT [true, true] with hσ4
  have e5 := runLoop_exec cap (cR 1) rT T hr1.symm (emitPair T rT true) [true, true] 15 (hP true) (8 * kh) σ4
    (by simp [hσ4, hσ3, Function.update_of_ne hr1.symm]) (by simp [hσ4, hσ3, hσ2, hσ1, ho])
    (by simp [hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hr1]; omega) (by omega)
  set σ5 := (appendO σ4 T rT (List.replicate (8 * kh) [true, true]).flatten).setv (cR 1) 0 with hσ5
  have h5o : σ5.sh T = (σ5.st T).length := by simp [hσ5, hσ4, hσ3, hσ2, hσ1, ho]; ring
  have h5r : σ5.val rT = σ.val rT + 4 + 16 * kh := by
    simp [hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hr1]; ring
  have e6 := emitPair_spec cap T rT false σ5 h5o (by omega)
  set σ6 := appendO σ5 T rT [true, false] with hσ6
  have e7 := dupsR_exec cap (cZ 3) (cR 1) cD (by pdst) (by pdst) (by pdst) 8 σ6
    (by simp [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hrD.symm, Function.update_of_ne (show cD ≠ cR 1 by pdst), hD])
    (by simp [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hrZ.symm, Function.update_of_ne hr1.symm,
      Function.update_of_ne (show cZ 3 ≠ cR 1 by pdst), hZ]; omega)
  have h6Z : σ6.val (cZ 3) = kh := by
    simp [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hrZ.symm, Function.update_of_ne (show cZ 3 ≠ cR 1 by pdst), hZ]
  have h6R : σ6.val (cR 1) = 0 := by simp [hσ6, hσ5, Function.update_of_ne hr1.symm]
  rw [h6Z, h6R, Nat.zero_add] at e7
  set σ7 := σ6.setv (cR 1) (8 * kh) with hσ7
  have e8 := runLoop_exec cap (cR 1) rT T hr1.symm (emitPair T rT false) [true, false] 15 (hP false) (8 * kh) σ7
    (by simp [hσ7]) (by simp [hσ7, hσ6, h5o])
    (by simp [hσ7, hσ6, Function.update_of_ne hr1, h5r]; omega) (by omega)
  set σ8 := (appendO σ7 T rT (List.replicate (8 * kh) [true, false]).flatten).setv (cR 1) 0 with hσ8
  have e9 := emitPair_spec cap T rT true σ8 (by simp [hσ8, hσ7, hσ6, h5o]; ring)
    (by simp [hσ8, hσ7, hσ6, Function.update_of_ne hr1, h5r]; omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6
    (WExec.seq e7 (WExec.seq e8 e9)))))))) ?_ (by unfold tableCost; omega)
  rw [tableHead_eq]
  simp only [hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1]
  simp only [← appendO_setv _ _ _ _ hr1.symm, wsetv_setv, appendO_append]
  rw [show σ.setv (cR 1) 0 = σ by rw [← h1, wsetv_same]]


/-! ## Before the first walk -/

/-- **The state before the first walk**: the table head, the walk index `0`, the bound `16 kh + 8`, the fixed part
of the requests rewound, the flag set. -/
def walkStart {ns : ℕ} (HS CT T : Fin (ns + 1)) : WM ns lnr :=
  .seq (tableStart T)
  (.seq (repeatP (zeroField CT (cY 3)) 8)
  (.seq (NearCubicGates.Close.Codec.rewindLoop CT (cY 3))
  (.seq (dupsR (cZ 3) cLC cD 16)
  (.seq (incs4 cLC) (.seq (incs4 cLC)
  (.seq (NearCubicGates.Close.Codec.rewindLoop HS rH) (.inc cNX)))))))

/-- The cost of `walkStart`. -/
def walkStartCost (kh h : ℕ) : ℕ :=
  tableCost kh + 1 + (8 * (60 * kh + 30 + 1) + 1 + (5 * (8 * (2 * kh + 1)) + 1 + 1 + (16 * (18 * kh + 4) + 1 +
    (15 + 1 + (15 + 1 + (5 * h + 1 + 1 + 3))))))

theorem walkStart_exec {ns : ℕ} (HS CT T : Fin (ns + 1)) (hHC : HS ≠ CT) (hHT : HS ≠ T) (hCT : CT ≠ T)
    (σ : WState ns lnr) (kh : ℕ) (hZ : σ.val (cZ 3) = kh) (h1 : σ.val (cR 1) = 0) (hD : σ.val cD = 0)
    (hY : σ.val (cY 3) = 0) (hL : σ.val cLC = 0) (hN : σ.val cNX = 0)
    (hT : σ.sh T = (σ.st T).length) (hC : σ.st CT = []) (hCh : σ.sh CT = 0)
    (hH : σ.sh HS = σ.val rH) (hc : σ.val rT + 40 * kh + 20 + 16 * kh + 8 + σ.val rH ≤ cap) :
    WExec cap (walkStart HS CT T) σ
      ((((((appendO (appendO σ T rT (tableHead kh)) CT (cY 3) ((walkDigits kh 8 0).flatMap (countField kh))).setv
        (cY 3) 0).seth CT 0).setv cLC (16 * kh + 8)).setv rH 0).seth HS 0 |>.setv cNX 1)
      (walkStartCost kh (σ.val rH)) := by
  have hcl : (countField kh 0).length = 2 * kh + 1 := by simp [countField_zero]; ring
  have e1 := tableStart_exec cap T σ kh hZ h1 hD hT (by omega)
  set σ1 := appendO σ T rT (tableHead kh) with hσ1
  have hr3 : rT ≠ cY 3 := by pdst
  have e2 := repeatP_exec cap CT (cY 3) (zeroField CT (cY 3)) (countField kh 0) (60 * kh + 30) (2 * kh)
    (fun τ => τ.val (cZ 3) = kh ∧ τ.val (cR 1) = 0 ∧ τ.val cD = 0)
    (fun τ h => ⟨by simp [Function.update_of_ne (show cZ 3 ≠ cY 3 by pdst), h.1],
      by simp [Function.update_of_ne (show cR 1 ≠ cY 3 by pdst), h.2.1],
      by simp [Function.update_of_ne (show cD ≠ cY 3 by pdst), h.2.2]⟩)
    (fun τ h ho hc' => zeroField_exec cap CT (cY 3) (by pdst) (by pdst) (by pdst) τ kh h.1 h.2.1 h.2.2 ho
      hc')
    8 σ1
    ⟨by simp [hσ1, Function.update_of_ne (show cZ 3 ≠ rT by pdst), hZ],
      by simp [hσ1, Function.update_of_ne (show cR 1 ≠ rT by pdst), h1],
      by simp [hσ1, Function.update_of_ne (show cD ≠ rT by pdst), hD]⟩
    (by simp [hσ1, Function.update_of_ne hCT, hC, hCh])
    (by simp [hσ1, Function.update_of_ne hr3.symm, hY, hcl]; omega)
  have hFl : ((List.replicate 8 (countField kh 0)).flatten).length = 8 * (2 * kh + 1) := by
    simp only [List.replicate_succ, List.replicate_zero, List.flatten_cons, List.flatten_nil, List.length_append,
      List.length_nil, hcl]; ring
  set σ2 := appendO σ1 CT (cY 3) (List.replicate 8 (countField kh 0)).flatten with hσ2
  have e3 := NearCubicGates.Close.Codec.rewindLoop_spec cap CT (cY 3) (8 * (2 * kh + 1)) σ2
    (by simp only [hσ2, hσ1, appendO_val, Function.update_self, Function.update_of_ne hr3.symm, hY, hFl,
      Nat.zero_add])
    (by simp only [hσ2, hσ1, appendO_sh, Function.update_self, Function.update_of_ne hCT, hCh, hFl, Nat.zero_add,
      le_refl]) (by omega)
  have h2sh : σ2.sh CT - 8 * (2 * kh + 1) = 0 := by
    simp only [hσ2, hσ1, appendO_sh, Function.update_self, Function.update_of_ne hCT, hCh, hFl, Nat.zero_add,
      Nat.sub_self]
  rw [h2sh] at e3
  set σ3 := (σ2.setv (cY 3) 0).seth CT 0 with hσ3
  have h3Z : σ3.val (cZ 3) = kh := by
    simp [hσ3, hσ2, hσ1, Function.update_of_ne (show cZ 3 ≠ cY 3 by pdst), Function.update_of_ne (show cZ 3 ≠ rT by pdst), hZ]
  have h3L : σ3.val cLC = 0 := by
    simp [hσ3, hσ2, hσ1, Function.update_of_ne (show cLC ≠ cY 3 by pdst), Function.update_of_ne (show cLC ≠ rT by pdst), hL]
  have e4 := dupsR_exec cap (cZ 3) cLC cD (by pdst) (by pdst) (by pdst) 16 σ3
    (by simp [hσ3, hσ2, hσ1, Function.update_of_ne (show cD ≠ cY 3 by pdst), Function.update_of_ne (show cD ≠ rT by pdst), hD])
    (by rw [h3Z, h3L]; omega)
  rw [h3Z, h3L, Nat.zero_add] at e4
  have e5 := incs4_exec cap cLC (σ3.setv cLC (16 * kh)) (by simp; omega)
  have e6 := incs4_exec cap cLC ((σ3.setv cLC (16 * kh)).setv cLC ((σ3.setv cLC (16 * kh)).val cLC + 4))
    (by simp; omega)
  rw [wsetv_setv, wsetv_setv] at e6
  rw [wsetv_setv] at e5
  simp only [WState.setv_val, Function.update_self] at e5 e6
  set σ6 := σ3.setv cLC (16 * kh + 4 + 4) with hσ6
  have h6H : σ6.val rH = σ.val rH := by
    simp [hσ6, hσ3, hσ2, hσ1, Function.update_of_ne (show rH ≠ cLC by pdst), Function.update_of_ne (show rH ≠ cY 3 by pdst),
      Function.update_of_ne (show rH ≠ rT by pdst)]
  have e7 := NearCubicGates.Close.Codec.rewindLoop_spec cap HS rH (σ.val rH) σ6 h6H
    (by simp [hσ6, hσ3, hσ2, hσ1, Function.update_of_ne hHC, Function.update_of_ne hHT, hH]) (by omega)
  have h6sh : σ6.sh HS - σ.val rH = 0 := by
    simp [hσ6, hσ3, hσ2, hσ1, Function.update_of_ne hHC, Function.update_of_ne hHT, hH]
  rw [h6sh] at e7
  set σ7 := (σ6.setv rH 0).seth HS 0 with hσ7
  have h7N : σ7.val cNX = 0 := by
    simp [hσ7, hσ6, hσ3, hσ2, hσ1, Function.update_of_ne (show cNX ≠ rH by pdst), Function.update_of_ne (show cNX ≠ cLC by pdst),
      Function.update_of_ne (show cNX ≠ cY 3 by pdst), Function.update_of_ne (show cNX ≠ rT by pdst), hN]
  have e8 := WExec.inc (cap := cap) cNX σ7 (by omega)
  rw [h7N] at e8
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6
    (WExec.seq e7 e8))))))) ?_ (by unfold walkStartCost; omega)
  rw [hσ7, hσ6, hσ3, hσ2, fields_zero]

end NearQuarticWires.Control
