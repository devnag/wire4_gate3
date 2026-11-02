import Proof.Quartic.Control.Gamma

/-!
# Loops of the coefficient-stage prelude

Paper: `cor:conditional`, paper/paper.tex, and Step 3: before the walks, the coefficient
stage reads the seed parameters `ℓ`, `kh = k/2`, `Q` and the prefix `π` from the child input, and prepares the fixed
part of the requests (`Control.requestHead`), the walk index and the table.

* `binary_prefixValue`, `countField_prefix`: the prefix `π` is the count field `1^{|π|} 0 π` of the number
  `prefixValue π`, which the number transcoder `Codec.numW` turns into `natWord (prefixValue π)`;
* `natWord_two_pow`: the number of walks `2^E` is written `1^{E+1} 0 0^E 1`;
* `runLoop`, `runLoop_exec`: append `m` copies of a word, for a register `m`;
* `frameScan`: walk through a framed word stored on a marked stream, running a program at each bit
  (`skipFrame_exec`, `onesScan_exec`, `bitsScan_exec`);
* `sentinelRewind`, `sentinelRewind_exec`: bring the head of the table back to its start, behind two zero cells.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearQuarticWires.Control

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.RepairOrdinary.Streaming (marks marks_length marks_append)
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat (appendO appendO_st appendO_sh appendO_val appendO_cell
  appendO_append appendO_setv)

/-! ## Words -/

theorem binary_prefixValue (π : List Bool) : binary π.length (Algorithm.CellCall.prefixValue π) = π := by
  induction π with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.length_cons, binary, Algorithm.CellCall.prefixValue]
    have h2 : ((if b then 1 else 0) + 2 * Algorithm.CellCall.prefixValue bs) / 2 =
        Algorithm.CellCall.prefixValue bs := by cases b <;> simp <;> omega
    rw [h2, ih]
    cases b <;> simp

/-- The prefix `π` is the count field of its number. -/
theorem countField_prefix (π : List Bool) :
    countField π.length (Algorithm.CellCall.prefixValue π) = List.replicate π.length true ++ false :: π := by
  rw [countField, binary_prefixValue]

theorem binary_zero (n : ℕ) : binary n 0 = List.replicate n false := by
  induction n with
  | zero => rfl
  | succ n ih => simp [binary, ih, List.replicate_succ]

/-- The count field of the digit `0`. -/
theorem countField_zero (kh : ℕ) : countField kh 0 = List.replicate kh true ++ false :: List.replicate kh false := by
  rw [countField, binary_zero]

theorem binary_two_pow (E : ℕ) : binary (E + 1) (2 ^ E) = List.replicate E false ++ [true] := by
  induction E with
  | zero => rfl
  | succ E ih =>
    rw [binary, show 2 ^ (E + 1) / 2 = 2 ^ E by rw [pow_succ]; simp, ih]
    simp [pow_succ, List.replicate_succ]

theorem natBitLength_two_pow (E : ℕ) : natBitLength (2 ^ E) = E + 1 := by
  simp [natBitLength, Nat.log_pow]

/-- The number of walks `2^E`. -/
theorem natWord_two_pow (E : ℕ) :
    natWord (2 ^ E) = List.replicate (E + 1) true ++ false :: (List.replicate E false ++ [true]) := by
  rw [NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_eq, natBitLength_two_pow,
    NearCubicGates.Close.Codec.fixedWidthNatBits_eq_binary, binary_two_pow]

theorem marks_frame_cons (b : Bool) (u : List Bool) :
    marks (frame (b :: u)) = [true, true, true, b] ++ marks (frame u) := by
  rw [NearCubicGates.Close.Codec.frame_eq_marks, NearCubicGates.Close.Codec.frame_eq_marks]
  simp [marks]

theorem marks_frame_nil : marks (frame []) = [true, false] := by
  rw [NearCubicGates.Close.Codec.frame_eq_marks]; simp [marks]

theorem marks_frame_length (u : List Bool) : (marks (frame u)).length = 4 * u.length + 2 := by
  rw [NearCubicGates.Close.Codec.frame_eq_marks, marks_length]; simp; ring

theorem rtb_pre (pre l : List Bool) (k : ℕ) : readTapeBit (pre ++ l) (pre.length + k) = readTapeBit l k := by
  unfold readTapeBit
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp

variable {ns nr : ℕ} (cap : ℕ)

theorem seth_self (σ : WState ns nr) (i : Fin (ns + 1)) : σ.seth i (σ.sh i) = σ := by
  refine WState.eq ?_ rfl rfl rfl
  funext q; by_cases hq : q = i
  · subst hq; simp
  · simp [Function.update_of_ne hq]

theorem fwd_at (W : Fin (ns + 1)) (σ : WState ns nr) (x : ℕ) :
    WExec cap (.fwd W) (σ.seth W x) (σ.seth W (x + 1)) 1 := by
  have := WExec.fwd (cap := cap) W (σ.seth W x)
  refine WExec.cast cap this ?_ le_rfl
  rw [seth_seth]; simp

theorem bwd_at (W : Fin (ns + 1)) (σ : WState ns nr) (x : ℕ) :
    WExec cap (.bwd W) (σ.seth W x) (σ.seth W (x - 1)) 1 := by
  have := WExec.bwd (cap := cap) W (σ.seth W x)
  refine WExec.cast cap this ?_ le_rfl
  rw [seth_seth]; simp

/-- `emitC` appends one cell. -/
theorem emitC_app (O : Fin (ns + 1)) (OP : Fin nr) (b : Bool) (σ : WState ns nr) (hO : σ.sh O = (σ.st O).length)
    (hc : σ.val OP < cap) : WExec cap (emitC O OP b) σ (appendO σ O OP [b]) 7 := by
  have := emitC_spec cap O OP b σ hO hc
  refine WExec.cast cap this ?_ le_rfl
  simp [appendO]

/-! ## Repetition -/

/-- `m` times `P`, for the register `K = m` (cleared). -/
def runLoop (K : Fin nr) (P : WM ns nr) : WM ns nr := .whr K (.seq (.dec K) P)

/-- **Repetition of an append.** If `P` appends `u` to `o`, `runLoop K P` appends `m` copies of `u`. -/
theorem runLoop_exec (K OP : Fin nr) (o : Fin (ns + 1)) (hK : K ≠ OP) (P : WM ns nr) (u : List Bool) (c : ℕ)
    (hP : ∀ σ : WState ns nr, σ.sh o = (σ.st o).length → σ.val OP + u.length ≤ cap →
      WExec cap P σ (appendO σ o OP u) c) :
    ∀ (m : ℕ) (σ : WState ns nr), σ.val K = m → σ.sh o = (σ.st o).length → σ.val OP + m * u.length ≤ cap →
      m ≤ cap → WExec cap (runLoop K P) σ ((appendO σ o OP (List.replicate m u).flatten).setv K 0) (m * (c + 4) + 1)
  | 0, σ, h0, _, _, _ => by
    refine WExec.cast cap (WExec.whrF h0) ?_ (by simp)
    rw [List.replicate_zero, List.flatten_nil, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO_nil, ← h0,
      wsetv_same]
  | m + 1, σ, hm, ho, hc, hmc => by
    have e1 := WExec.dec (cap := cap) K σ (by omega)
    rw [hm, Nat.add_sub_cancel] at e1
    have e2 := hP (σ.setv K m) (by simpa using ho) (by simp [Function.update_of_ne hK.symm]; nlinarith)
    have e3 := runLoop_exec K OP o hK P u c hP m (appendO (σ.setv K m) o OP u)
      (by simp [Function.update_of_ne hK]) (by simp [ho]) (by simp [Function.update_of_ne hK.symm]; nlinarith)
      (by omega)
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq e1 e2) e3) ?_ (by ring_nf; omega)
    rw [appendO_append, appendO_setv _ _ _ _ hK, wsetv_setv,
      List.replicate_succ, List.flatten_cons]

/-! ## Framed words on a marked stream -/

/-- One bit of a framed word on a marked stream: from the cell after the mark of the bit's own mark, run `P` at the
bit, and stop at the same place of the next bit. -/
def scanBody (W : Fin (ns + 1)) (P : WM ns nr) : WM ns nr :=
  .seq (.fwd W) (.seq (.fwd W) (.seq P (.seq (.fwd W) (.fwd W))))

/-- **A framed word on a marked stream**: `P` at each bit, the head past the word. -/
def frameScan (W : Fin (ns + 1)) (P : WM ns nr) : WM ns nr :=
  .seq (.fwd W) (.seq (.whs W (scanBody W P)) (.fwd W))

theorem frameScan_bit (W : Fin (ns + 1)) (b : Bool) (u pre rest : List Bool) (σ : WState ns nr)
    (hst : σ.st W = pre ++ marks (frame (b :: u)) ++ rest) : wbit (σ.seth W (pre.length + 1)) W = true := by
  simp only [wbit, WState.seth_st, WState.seth_sh, Function.update_self, hst, marks_frame_cons, List.append_assoc]
  rw [rtb_pre]; rfl

theorem frameScan_at (W : Fin (ns + 1)) (b : Bool) (u pre rest : List Bool) (σ : WState ns nr)
    (hst : σ.st W = pre ++ marks (frame (b :: u)) ++ rest) : wbit (σ.seth W (pre.length + 3)) W = b := by
  simp only [wbit, WState.seth_st, WState.seth_sh, Function.update_self, hst, marks_frame_cons, List.append_assoc]
  rw [rtb_pre]; rfl

theorem frameScan_end (W : Fin (ns + 1)) (pre rest : List Bool) (σ : WState ns nr)
    (hst : σ.st W = pre ++ marks (frame []) ++ rest) : wbit (σ.seth W (pre.length + 1)) W = false := by
  simp only [wbit, WState.seth_st, WState.seth_sh, Function.update_self, hst, marks_frame_nil, List.append_assoc]
  rw [rtb_pre]; rfl

theorem frameScan_tail (W : Fin (ns + 1)) (b : Bool) (u pre rest : List Bool) (σ : WState ns nr)
    (hst : σ.st W = pre ++ marks (frame (b :: u)) ++ rest) :
    σ.st W = (pre ++ [true, true, true, b]) ++ marks (frame u) ++ rest := by
  rw [hst, marks_frame_cons]; simp [List.append_assoc]

/-- **Moving past a framed word** stored on a marked stream. -/
theorem skipLoop_frame (W : Fin (ns + 1)) :
    ∀ (u pre rest : List Bool) (σ : WState ns nr), σ.st W = pre ++ marks (frame u) ++ rest →
      WExec cap (.whs W (scanBody W .skip)) (σ.seth W (pre.length + 1)) (σ.seth W (pre.length + 1 + 4 * u.length))
        (10 * u.length + 1)
  | [], pre, rest, σ, hst => by
    refine WExec.cast cap (WExec.whsF (frameScan_end W pre rest σ hst)) ?_ (by simp)
    simp
  | b :: u, pre, rest, σ, hst => by
    have e1 := fwd_at cap W σ (pre.length + 1)
    have e2 := fwd_at cap W σ (pre.length + 1 + 1)
    have e3 := WExec.skip (cap := cap) (σ.seth W (pre.length + 1 + 1 + 1))
    have e4 := fwd_at cap W σ (pre.length + 1 + 1 + 1)
    have e5 := fwd_at cap W σ (pre.length + 1 + 1 + 1 + 1)
    have e6 := skipLoop_frame W u (pre ++ [true, true, true, b]) rest σ (frameScan_tail W b u pre rest σ hst)
    have hlen : (pre ++ [true, true, true, b]).length + 1 = pre.length + 1 + 1 + 1 + 1 + 1 := by
      simp only [List.length_append, List.length_cons, List.length_nil]
    rw [hlen] at e6
    refine WExec.cast cap (WExec.whsT (frameScan_bit W b u pre rest σ hst)
      (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5)))) e6) ?_ (by simp; omega)
    congr 1; simp; omega

/-- **Moving past a framed word** on a marked stream: from its first cell to the cell after it. -/
theorem skipFrame_exec (W : Fin (ns + 1)) (u pre rest : List Bool) (σ : WState ns nr)
    (hst : σ.st W = pre ++ marks (frame u) ++ rest) (hsh : σ.sh W = pre.length) :
    WExec cap (frameScan W .skip) σ (σ.seth W (pre.length + (marks (frame u)).length)) (10 * u.length + 5) := by
  have e0 : WExec cap (.fwd W) σ (σ.seth W (pre.length + 1)) 1 := by
    have := fwd_at cap W σ pre.length
    rw [← hsh, seth_self] at this
    rw [← hsh]; exact this
  have e1 := skipLoop_frame cap W u pre rest σ hst
  have e2 := fwd_at cap W σ (pre.length + 1 + 4 * u.length)
  refine WExec.cast cap (WExec.seq e0 (WExec.seq e1 e2)) ?_ (by omega)
  rw [marks_frame_length]; congr 1; omega


/-! ## The prefix `π`: its ones, then its bits -/

/-- Four increments. -/
def incs4 (R : Fin nr) : WM ns nr := .seq (.inc R) (.seq (.inc R) (.seq (.inc R) (.inc R)))

theorem incs4_exec (R : Fin nr) (σ : WState ns nr) (h : σ.val R + 4 ≤ cap) :
    WExec cap (incs4 R) σ (σ.setv R (σ.val R + 4)) 15 := by
  have e1 := WExec.inc (cap := cap) R σ (by omega)
  have e2 := WExec.inc (cap := cap) R (σ.setv R (σ.val R + 1)) (by simp; omega)
  have e3 := WExec.inc (cap := cap) R ((σ.setv R (σ.val R + 1)).setv R ((σ.setv R (σ.val R + 1)).val R + 1))
    (by simp; omega)
  have e4 := WExec.inc (cap := cap) R (((σ.setv R (σ.val R + 1)).setv R ((σ.setv R (σ.val R + 1)).val R + 1)).setv R
    (((σ.setv R (σ.val R + 1)).setv R ((σ.setv R (σ.val R + 1)).val R + 1)).val R + 1)) (by simp; omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4))) ?_ (by omega)
  simp only [wsetv_setv, WState.setv_val, Function.update_self]

/-- At each bit of `π`: one `1` on `T`, four cells counted in `RC`. -/
def onesP (T : Fin (ns + 1)) (OPT RC : Fin nr) : WM ns nr := .seq (emitC T OPT true) (incs4 RC)

theorem onesP_exec (T : Fin (ns + 1)) (OPT RC : Fin nr) (hOR : OPT ≠ RC) (σ : WState ns nr)
    (hT : σ.sh T = (σ.st T).length) (hc : σ.val OPT < cap) (hr : σ.val RC + 4 ≤ cap) :
    WExec cap (onesP T OPT RC) σ ((appendO σ T OPT [true]).setv RC (σ.val RC + 4)) 23 := by
  have e1 := emitC_app cap T OPT true σ hT hc
  have e2 := incs4_exec cap RC (appendO σ T OPT [true]) (by simp [Function.update_of_ne hOR.symm]; omega)
  refine WExec.cast cap (WExec.seq e1 e2) ?_ (by omega)
  simp [Function.update_of_ne hOR.symm]

/-- At each bit of `π`: the bit on `T`. -/
def bitP (W T : Fin (ns + 1)) (OPT : Fin nr) : WM ns nr := .ifs W (emitC T OPT true) (emitC T OPT false)

theorem bitP_exec (W T : Fin (ns + 1)) (OPT : Fin nr) (σ : WState ns nr) (b : Bool) (hb : wbit σ W = b)
    (hT : σ.sh T = (σ.st T).length) (hc : σ.val OPT < cap) :
    WExec cap (bitP W T OPT) σ (appendO σ T OPT [b]) 8 := by
  cases b
  · exact WExec.ifsF hb (emitC_app cap T OPT false σ hT hc)
  · exact WExec.ifsT hb (emitC_app cap T OPT true σ hT hc)

theorem seth_setv (σ : WState ns nr) (W : Fin (ns + 1)) (x : ℕ) (r : Fin nr) (v : ℕ) :
    (σ.seth W x).setv r v = (σ.setv r v).seth W x := rfl

/-- The scan of the ones. -/
theorem onesLoop_frame (W T : Fin (ns + 1)) (hWT : W ≠ T) (OPT RC : Fin nr) (hOR : OPT ≠ RC) :
    ∀ (u pre rest : List Bool) (σ : WState ns nr), σ.st W = pre ++ marks (frame u) ++ rest →
      σ.sh T = (σ.st T).length → σ.val OPT + u.length ≤ cap → σ.val RC + 4 * u.length ≤ cap →
      WExec cap (.whs W (scanBody W (onesP T OPT RC))) (σ.seth W (pre.length + 1))
        (((appendO σ T OPT (List.replicate u.length true)).setv RC (σ.val RC + 4 * u.length)).seth W
          (pre.length + 1 + 4 * u.length)) (33 * u.length + 1)
  | [], pre, rest, σ, hst, _, _, _ => by
    refine WExec.cast cap (WExec.whsF (frameScan_end W pre rest σ hst)) ?_ (by simp)
    simp only [List.length_nil, List.replicate_zero, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO_nil,
      Nat.mul_zero, Nat.add_zero, wsetv_same]
  | b :: u, pre, rest, σ, hst, hT, hc, hr => by
    have e1 := fwd_at cap W σ (pre.length + 1)
    have e2 := fwd_at cap W σ (pre.length + 1 + 1)
    have e3 := onesP_exec cap T OPT RC hOR (σ.seth W (pre.length + 1 + 1 + 1))
      (by simp [Function.update_of_ne hWT.symm, hT]) (by simp; simp at hc; omega) (by simp; simp at hr; omega)
    set σ1 := (appendO σ T OPT [true]).setv RC (σ.val RC + 4) with hσ1
    have hσ1' : (appendO (σ.seth W (pre.length + 1 + 1 + 1)) T OPT [true]).setv RC
        ((σ.seth W (pre.length + 1 + 1 + 1)).val RC + 4) = σ1.seth W (pre.length + 1 + 1 + 1) := by
      rw [← appendO_seth_comm _ _ _ hWT]; rfl
    rw [hσ1'] at e3
    have e4 := fwd_at cap W σ1 (pre.length + 1 + 1 + 1)
    have e5 := fwd_at cap W σ1 (pre.length + 1 + 1 + 1 + 1)
    have h1W : σ1.st W = (pre ++ [true, true, true, b]) ++ marks (frame u) ++ rest := by
      simp [hσ1, Function.update_of_ne hWT, frameScan_tail W b u pre rest σ hst]
    have e6 := onesLoop_frame W T hWT OPT RC hOR u (pre ++ [true, true, true, b]) rest σ1 h1W
      (by simp [hσ1, hT]) (by simp [hσ1, Function.update_of_ne hOR]; simp at hc; omega)
      (by simp [hσ1]; simp at hr; omega)
    have hlen : (pre ++ [true, true, true, b]).length + 1 = pre.length + 1 + 1 + 1 + 1 + 1 := by
      simp only [List.length_append, List.length_cons, List.length_nil]
    rw [hlen] at e6
    have hpos : pre.length + 1 + 1 + 1 + 1 + 1 + 4 * u.length = pre.length + 1 + 4 * (b :: u).length := by
      simp only [List.length_cons]; ring
    have hrep : [true] ++ List.replicate u.length true = List.replicate (b :: u).length true := by
      simp [List.replicate_succ]
    have hv : ((appendO σ T OPT [true]).setv RC (σ.val RC + 4)).val RC + 4 * u.length =
        σ.val RC + 4 * (b :: u).length := by
      simp only [WState.setv_val, Function.update_self, List.length_cons]; ring
    refine WExec.cast cap (WExec.whsT (frameScan_bit W b u pre rest σ hst)
      (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5)))) e6) ?_
      (by simp only [List.length_cons]; omega)
    rw [hpos, hσ1, appendO_setv _ _ _ _ hOR.symm, wsetv_setv, appendO_append, hrep, hv]

/-- The scan of the bits. -/
theorem bitsLoop_frame (W T : Fin (ns + 1)) (hWT : W ≠ T) (OPT : Fin nr) :
    ∀ (u pre rest : List Bool) (σ : WState ns nr), σ.st W = pre ++ marks (frame u) ++ rest →
      σ.sh T = (σ.st T).length → σ.val OPT + u.length ≤ cap →
      WExec cap (.whs W (scanBody W (bitP W T OPT))) (σ.seth W (pre.length + 1))
        ((appendO σ T OPT u).seth W (pre.length + 1 + 4 * u.length)) (18 * u.length + 1)
  | [], pre, rest, σ, hst, _, _ => by
    refine WExec.cast cap (WExec.whsF (frameScan_end W pre rest σ hst)) ?_ (by simp)
    simp only [List.length_nil, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO_nil, Nat.mul_zero,
      Nat.add_zero]
  | b :: u, pre, rest, σ, hst, hT, hc => by
    have e1 := fwd_at cap W σ (pre.length + 1)
    have e2 := fwd_at cap W σ (pre.length + 1 + 1)
    have e3 := bitP_exec cap W T OPT (σ.seth W (pre.length + 1 + 1 + 1)) b
      (by have := frameScan_at W b u pre rest σ hst; simpa using this)
      (by simp [Function.update_of_ne hWT.symm, hT]) (by simp; simp at hc; omega)
    set σ1 := appendO σ T OPT [b] with hσ1
    rw [← appendO_seth_comm _ _ _ hWT] at e3
    have e4 := fwd_at cap W σ1 (pre.length + 1 + 1 + 1)
    have e5 := fwd_at cap W σ1 (pre.length + 1 + 1 + 1 + 1)
    have h1W : σ1.st W = (pre ++ [true, true, true, b]) ++ marks (frame u) ++ rest := by
      simp [hσ1, Function.update_of_ne hWT, frameScan_tail W b u pre rest σ hst]
    have e6 := bitsLoop_frame W T hWT OPT u (pre ++ [true, true, true, b]) rest σ1 h1W
      (by simp [hσ1, hT]) (by simp [hσ1]; simp at hc; omega)
    have hlen : (pre ++ [true, true, true, b]).length + 1 = pre.length + 1 + 1 + 1 + 1 + 1 := by
      simp only [List.length_append, List.length_cons, List.length_nil]
    rw [hlen] at e6
    have hpos : pre.length + 1 + 1 + 1 + 1 + 1 + 4 * u.length = pre.length + 1 + 4 * (b :: u).length := by
      simp only [List.length_cons]; ring
    refine WExec.cast cap (WExec.whsT (frameScan_bit W b u pre rest σ hst)
      (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5)))) e6) ?_
      (by simp only [List.length_cons]; omega)
    rw [hpos, hσ1, appendO_append, List.singleton_append]

/-! ## The table, back to its start -/

/-- Back to the start of `marks U` behind two zero cells. -/
def sentinelRewind (W : Fin (ns + 1)) : WM ns nr :=
  .seq (.bwd W) (.seq (.bwd W) (.seq (.whs W (.seq (.bwd W) (.bwd W))) (.seq (.fwd W) (.fwd W))))

theorem sentinelLoop (W : Fin (ns + 1)) (J U : List Bool) (σ : WState ns nr)
    (hst : σ.st W = J ++ [false, false] ++ marks U) :
    ∀ j, j ≤ U.length → WExec cap (.whs W (.seq (.bwd W) (.bwd W))) (σ.seth W (J.length + 2 * j)) (σ.seth W J.length)
      (5 * j + 1)
  | 0, _ => by
    refine WExec.cast cap (WExec.whsF ?_) (by simp) (by simp)
    simp only [wbit, WState.seth_st, WState.seth_sh, Function.update_self, hst, List.append_assoc, Nat.mul_zero,
      Nat.add_zero]
    have := rtb_pre J ([false, false] ++ marks U) 0
    rw [Nat.add_zero] at this
    rw [this]; rfl
  | j + 1, hj => by
    have hb : wbit (σ.seth W (J.length + 2 * (j + 1))) W = true := by
      simp only [wbit, WState.seth_st, WState.seth_sh, Function.update_self, hst]
      have h1 := rtb_pre (J ++ [false, false]) (marks U ++ []) (2 * j)
      simp only [List.append_nil, List.length_append, List.length_cons, List.length_nil] at h1
      rw [show J.length + 2 * (j + 1) = J.length + (0 + 1 + 1) + 2 * j by ring, h1]
      have := read_marks_mark U [] j (by omega)
      simpa using this
    have e1 := bwd_at cap W σ (J.length + 2 * (j + 1))
    have e2 := bwd_at cap W σ (J.length + 2 * (j + 1) - 1)
    have e3 := sentinelLoop W J U σ hst j (by omega)
    have hp : J.length + 2 * (j + 1) - 1 - 1 = J.length + 2 * j := by omega
    rw [hp] at e2
    exact WExec.cast cap (WExec.whsT hb (WExec.seq e1 e2) e3) rfl (by omega)

/-- **The table back to its start**: from the end of `J ++ [0, 0] ++ marks U` to the start of `marks U`. -/
theorem sentinelRewind_exec (W : Fin (ns + 1)) (J U : List Bool) (σ : WState ns nr)
    (hst : σ.st W = J ++ [false, false] ++ marks U) (hsh : σ.sh W = (σ.st W).length) :
    WExec cap (sentinelRewind W) σ (σ.seth W (J.length + 2)) (5 * U.length + 9) := by
  have hl : σ.sh W = J.length + 2 * U.length + 2 := by rw [hsh, hst]; simp [marks_length]; ring
  have e1 : WExec cap (.bwd W) σ (σ.seth W (J.length + 2 * U.length + 1)) 1 := by
    have := bwd_at cap W σ (σ.sh W)
    rw [seth_self, hl] at this; exact this
  have e2 := bwd_at cap W σ (J.length + 2 * U.length + 1)
  rw [Nat.add_sub_cancel] at e2
  have e3 := sentinelLoop cap W J U σ hst U.length le_rfl
  have e4 := fwd_at cap W σ J.length
  have e5 := fwd_at cap W σ (J.length + 1)
  exact WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5)))) rfl (by omega)


/-- **A framed word on a marked stream**, from the loop over its bits. -/
theorem frameScan_exec (W : Fin (ns + 1)) (P : WM ns nr) (u pre : List Bool) (σ τ : WState ns nr) (c : ℕ)
    (hsh : σ.sh W = pre.length)
    (hloop : WExec cap (.whs W (scanBody W P)) (σ.seth W (pre.length + 1)) (τ.seth W (pre.length + 1 + 4 * u.length))
      c) :
    WExec cap (frameScan W P) σ (τ.seth W (pre.length + (marks (frame u)).length)) (c + 4) := by
  have e0 : WExec cap (.fwd W) σ (σ.seth W (pre.length + 1)) 1 := by
    have := fwd_at cap W σ pre.length
    rw [← hsh, seth_self] at this
    rw [← hsh]; exact this
  have e2 := fwd_at cap W τ (pre.length + 1 + 4 * u.length)
  refine WExec.cast cap (WExec.seq e0 (WExec.seq hloop e2)) ?_ (by omega)
  rw [marks_frame_length]; congr 1; omega

end NearQuarticWires.Control
