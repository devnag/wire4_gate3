import Proof.Quartic.Control.Budget
import Proof.Gates.Codec.FieldNum

/-!
# Counting through the closed walks

Paper: Step 3 of `sec:algorithm`, paper/paper.tex, and `prop:time`: a child evaluation computes
one coefficient for each of the `N^{2m} = 2^{mk}` closed walks `w = (u_1, v_1, …, u_m, v_m)`, `N = 2^{k/2}`, in the
order of their base-`N` index (`Greedy.walkList`, slot `0` the lowest digit).

The walk index is kept as `2m` count fields `1^{kh} 0 b_0 … b_{kh−1}` (`countField`), one per slot, the bits of the
slot lowest first. A count field is the input of the number transcoder `Codec.numW` (imported from
`Proof.Gates.Codec.FieldNum`), which writes `marks (natWord v)`: this is how a request names a walk. Incrementing
the index adds a carry through the bits of the fields (`bitsInc`, `bitsInc_binary`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.Control

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.RepairOrdinary.Streaming (marks marks_length marks_append)

/-- A count field of width `kh`: `kh` ones, a zero, then the `kh` bits of `v`, lowest first. -/
def countField (kh v : ℕ) : List Bool := List.replicate kh true ++ false :: binary kh v

/-- Adding a carry to a bit list, lowest bit first: the new bits and the carry out. -/
def bitsInc : List Bool → Bool → List Bool × Bool
  | [], c => ([], c)
  | b :: bs, c =>
    if c then (if b then (false :: (bitsInc bs true).1, (bitsInc bs true).2) else (true :: bs, false))
    else (b :: bs, false)

theorem bitsInc_false (bs : List Bool) : bitsInc bs false = (bs, false) := by
  cases bs <;> simp [bitsInc]

theorem bitsInc_length (bs : List Bool) (c : Bool) : (bitsInc bs c).1.length = bs.length := by
  induction bs generalizing c with
  | nil => rfl
  | cons b bs ih => cases c <;> cases b <;> simp [bitsInc, ih]

/-- **Adding a carry to `kh` bits** of `d < 2^kh` gives the bits of `(d + c) mod 2^kh`, and the carry out
`d + c = 2^kh`. -/
theorem bitsInc_binary (kh d : ℕ) (hd : d < 2 ^ kh) (c : Bool) :
    bitsInc (binary kh d) c = (binary kh ((d + c.toNat) % 2 ^ kh), decide (d + c.toNat = 2 ^ kh)) := by
  induction kh generalizing d c with
  | zero =>
    have : d = 0 := by simpa using hd
    subst this
    cases c <;> simp [binary, bitsInc]
  | succ kh ih =>
    cases c
    · simp only [Bool.toNat_false, Nat.add_zero, Nat.mod_eq_of_lt hd, bitsInc_false]
      simp; omega
    · have hd2 : d / 2 < 2 ^ kh := by rw [pow_succ] at hd; omega
      rcases Nat.mod_two_eq_zero_or_one d with h | h
      · -- the lowest bit is `0`
        have hb : (d % 2 == 1) = false := by simp [h]
        simp only [binary, hb, bitsInc, if_true, Bool.false_eq_true, if_false, Bool.toNat_true]
        have hlt : d + 1 < 2 ^ (kh + 1) := by rw [pow_succ]; omega
        rw [Nat.mod_eq_of_lt hlt]
        have h1 : (d + 1) % 2 = 1 := by omega
        have h2 : (d + 1) / 2 = d / 2 := by omega
        simp [binary, h1, h2]
        omega
      · -- the lowest bit is `1`
        have hb : (d % 2 == 1) = true := by simp [h]
        simp only [binary, hb, bitsInc, if_true, Bool.toNat_true]
        rw [ih (d / 2) hd2 true]
        simp only [Bool.toNat_true]
        rcases Nat.lt_or_ge (d / 2 + 1) (2 ^ kh) with hl | hl
        · have hm : (d / 2 + 1) % 2 ^ kh = d / 2 + 1 := Nat.mod_eq_of_lt hl
          have hlt : d + 1 < 2 ^ (kh + 1) := by rw [pow_succ]; omega
          rw [hm, Nat.mod_eq_of_lt hlt]
          have h1 : (d + 1) % 2 = 0 := by omega
          have h2 : (d + 1) / 2 = d / 2 + 1 := by omega
          simp [binary, h1, h2]
          constructor <;> omega
        · have he : d / 2 + 1 = 2 ^ kh := by omega
          have hd1 : d + 1 = 2 ^ (kh + 1) := by rw [pow_succ]; omega
          simp only [he, hd1, Nat.mod_self]
          simp [binary]


/-! ## Adding the carry on a stream -/

section BitsLoop

variable {ns nr : ℕ} (cap : ℕ)

/-- Add the carry `CY` (`0` or `1`) to the next `U` bits of the raw stream `CT`, lowest first. -/
def bitsLoop (CT : Fin (ns + 1)) (CY U : Fin nr) : WMX ns nr :=
  .whr U (.seq (WMX.dec U) (.seq (.ifr CY (.ifs CT (WMX.wr CT false) (.seq (WMX.wr CT true) (WMX.dec CY)))
    WMX.skip) (WMX.fwd CT)))

/-- The state during the carry loop. -/
def bitsSt (σ : WState ns nr) (CT : Fin (ns + 1)) (CY U : Fin nr) (content : List Bool) (h u c : ℕ) :
    WState ns nr :=
  (((σ.sets CT content).seth CT h).setv U u).setv CY c

theorem bitsLoop_exec (CT : Fin (ns + 1)) (CY U : Fin nr) (hCU : CY ≠ U) (σ : WState ns nr) (rest : List Bool) :
    ∀ (bs pre : List Bool) (c : Bool), bs.length ≤ cap → 1 ≤ cap →
      WXExec cap (bitsLoop CT CY U) (bitsSt σ CT CY U (pre ++ bs ++ rest) pre.length bs.length c.toNat)
        (bitsSt σ CT CY U (pre ++ (bitsInc bs c).1 ++ rest) (pre.length + bs.length) 0 (bitsInc bs c).2.toNat)
        (bs.length * 12 + 1)
  | [], pre, c, _, _ => by
    refine WXExec.mono (WXExec.whrF (by simp [bitsSt, Function.update_of_ne hCU.symm])) ?_
      |>.cast cap (by simp [bitsInc]) le_rfl
    omega
  | b :: bs, pre, c, hc, hc1 => by
    have hU : (bitsSt σ CT CY U (pre ++ (b :: bs) ++ rest) pre.length (b :: bs).length c.toNat).val U =
        bs.length + 1 := by simp [bitsSt, Function.update_of_ne hCU.symm]
    have e1 := WXExec.dec cap U (bitsSt σ CT CY U (pre ++ (b :: bs) ++ rest) pre.length (b :: bs).length c.toNat)
      (by rw [hU]; simp at hc; omega)
    rw [hU, Nat.add_sub_cancel] at e1
    have hτ1 : (bitsSt σ CT CY U (pre ++ (b :: bs) ++ rest) pre.length (b :: bs).length c.toNat).setv U bs.length =
        bitsSt σ CT CY U (pre ++ (b :: bs) ++ rest) pre.length bs.length c.toNat := by
      refine WState.eq rfl rfl ?_ rfl
      funext q; by_cases hq : q = U
      · subst hq; simp [bitsSt, Function.update_of_ne hCU.symm]
      · by_cases hq' : q = CY
        · subst hq'; simp [bitsSt, Function.update_of_ne hCU]
        · simp [bitsSt, Function.update_of_ne hq, Function.update_of_ne hq']
    rw [hτ1] at e1
    have hread : wbit (bitsSt σ CT CY U (pre ++ (b :: bs) ++ rest) pre.length bs.length c.toNat) CT = b := by
      simp only [wbit, bitsSt, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh,
        Function.update_self, List.append_assoc]
      rw [show pre.length = pre.length + 0 from rfl, NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.read_pre]
      rfl
    have hwr : ∀ v : Bool, writeTapeBit (pre ++ (b :: bs) ++ rest) pre.length v = pre ++ (v :: bs) ++ rest := by
      intro v
      have := NearCubicGates.Close.WorkerArith.wtb_mid pre (b :: bs ++ rest) v
      simpa [List.append_assoc] using this
    -- the step on the bit, then the head moves on
    have step : ∀ (b' : Bool) (c' : Bool), (c = true ∧ b = true ∧ b' = false ∧ c' = true) ∨
        (c = true ∧ b = false ∧ b' = true ∧ c' = false) ∨ (c = false ∧ b' = b ∧ c' = false) →
        WXExec cap (.seq (.ifr CY (.ifs CT (WMX.wr CT false) (.seq (WMX.wr CT true) (WMX.dec CY))) WMX.skip)
          (WMX.fwd CT)) (bitsSt σ CT CY U (pre ++ (b :: bs) ++ rest) pre.length bs.length c.toNat)
          (bitsSt σ CT CY U ((pre ++ [b']) ++ bs ++ rest) (pre ++ [b']).length bs.length c'.toNat) 7 := by
      intro b' c' hcase
      have hfwd : ∀ (cont : List Bool) (cc : ℕ),
          WXExec cap (WMX.fwd CT) (bitsSt σ CT CY U cont pre.length bs.length cc)
            (bitsSt σ CT CY U cont (pre ++ [b']).length bs.length cc) 1 := by
        intro cont cc
        refine WXExec.cast cap (WXExec.fwd cap CT _) ?_ le_rfl
        refine WState.eq ?_ rfl rfl rfl
        funext q; by_cases hq : q = CT
        · subst hq; simp [bitsSt]
        · simp [bitsSt, Function.update_of_ne hq]
      have hcont : (pre ++ [b']) ++ bs ++ rest = pre ++ (b' :: bs) ++ rest := by simp [List.append_assoc]
      rw [hcont]
      rcases hcase with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · have ew := WXExec.wr cap CT false (bitsSt σ CT CY U (pre ++ (true :: bs) ++ rest) pre.length bs.length
          (true : Bool).toNat)
        have hst : (bitsSt σ CT CY U (pre ++ (true :: bs) ++ rest) pre.length bs.length (true : Bool).toNat).sets CT
            (writeTapeBit ((bitsSt σ CT CY U (pre ++ (true :: bs) ++ rest) pre.length bs.length
              (true : Bool).toNat).st CT) ((bitsSt σ CT CY U (pre ++ (true :: bs) ++ rest) pre.length bs.length
              (true : Bool).toNat).sh CT) false) =
            bitsSt σ CT CY U (pre ++ (false :: bs) ++ rest) pre.length bs.length (true : Bool).toNat := by
          refine WState.eq ?_ ?_ rfl rfl
          · funext q; by_cases hq : q = CT
            · subst hq; simp [bitsSt]
            · simp [bitsSt, Function.update_of_ne hq]
          · funext q; by_cases hq : q = CT
            · subst hq; simpa [bitsSt, List.append_assoc] using hwr false
            · simp [bitsSt, Function.update_of_ne hq]
        rw [hst] at ew
        exact WXExec.mono (WXExec.seq (WXExec.ifrT (by simp [bitsSt]) (WXExec.ifsT (by rw [hread]) ew))
          (hfwd _ _)) (by omega)
      · have ew := WXExec.wr cap CT true (bitsSt σ CT CY U (pre ++ (false :: bs) ++ rest) pre.length bs.length
          (true : Bool).toNat)
        have hst : (bitsSt σ CT CY U (pre ++ (false :: bs) ++ rest) pre.length bs.length (true : Bool).toNat).sets CT
            (writeTapeBit ((bitsSt σ CT CY U (pre ++ (false :: bs) ++ rest) pre.length bs.length
              (true : Bool).toNat).st CT) ((bitsSt σ CT CY U (pre ++ (false :: bs) ++ rest) pre.length bs.length
              (true : Bool).toNat).sh CT) true) =
            bitsSt σ CT CY U (pre ++ (true :: bs) ++ rest) pre.length bs.length (true : Bool).toNat := by
          refine WState.eq ?_ ?_ rfl rfl
          · funext q; by_cases hq : q = CT
            · subst hq; simp [bitsSt]
            · simp [bitsSt, Function.update_of_ne hq]
          · funext q; by_cases hq : q = CT
            · subst hq; simpa [bitsSt, List.append_assoc] using hwr true
            · simp [bitsSt, Function.update_of_ne hq]
        rw [hst] at ew
        have ed := WXExec.dec cap CY (bitsSt σ CT CY U (pre ++ (true :: bs) ++ rest) pre.length bs.length
          (true : Bool).toNat) (by simp [bitsSt]; omega)
        have hd : (bitsSt σ CT CY U (pre ++ (true :: bs) ++ rest) pre.length bs.length (true : Bool).toNat).setv CY
            ((bitsSt σ CT CY U (pre ++ (true :: bs) ++ rest) pre.length bs.length (true : Bool).toNat).val CY - 1) =
            bitsSt σ CT CY U (pre ++ (true :: bs) ++ rest) pre.length bs.length (false : Bool).toNat := by
          refine WState.eq rfl rfl ?_ rfl
          funext q; by_cases hq : q = CY
          · subst hq; simp [bitsSt]
          · simp [bitsSt, Function.update_of_ne hq]
        rw [hd] at ed
        exact WXExec.mono (WXExec.seq (WXExec.ifrT (by simp [bitsSt]) (WXExec.ifsF (by rw [hread])
          (WXExec.seq ew ed))) (hfwd _ _)) (by omega)
      · exact WXExec.mono (WXExec.seq (WXExec.ifrF (by simp [bitsSt]) (WXExec.skip cap _)) (hfwd _ _)) (by omega)
    -- the rest of the loop
    have hU0 : (bitsSt σ CT CY U (pre ++ (b :: bs) ++ rest) pre.length (b :: bs).length c.toNat).val U ≠ 0 := by
      rw [hU]; omega
    have finish : ∀ (b' c' : Bool), ((c = true ∧ b = true ∧ b' = false ∧ c' = true) ∨
        (c = true ∧ b = false ∧ b' = true ∧ c' = false) ∨ (c = false ∧ b' = b ∧ c' = false)) →
        bitsInc (b :: bs) c = (b' :: (bitsInc bs c').1, (bitsInc bs c').2) →
        WXExec cap (bitsLoop CT CY U) (bitsSt σ CT CY U (pre ++ (b :: bs) ++ rest) pre.length (b :: bs).length c.toNat)
          (bitsSt σ CT CY U (pre ++ (bitsInc (b :: bs) c).1 ++ rest) (pre.length + (b :: bs).length) 0
            (bitsInc (b :: bs) c).2.toNat) ((b :: bs).length * 12 + 1) := by
      intro b' c' hcase hinc
      have e2 := step b' c' hcase
      have e3 := bitsLoop_exec CT CY U hCU σ rest bs (pre ++ [b']) c' (by simp at hc; omega) hc1
      refine WXExec.mono (WXExec.cast cap (WXExec.whrT hU0 (WXExec.seq e1 e2) e3) ?_ le_rfl) ?_
      · rw [hinc]; simp [List.append_assoc]; ring_nf
      · simp; omega
    cases c <;> cases b
    · exact finish false false (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)) (by simp [bitsInc, bitsInc_false])
    · exact finish true false (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)) (by simp [bitsInc, bitsInc_false])
    · exact finish true false (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩)) (by simp [bitsInc, bitsInc_false])
    · exact finish false true (Or.inl ⟨rfl, rfl, rfl, rfl⟩) (by simp [bitsInc])

end BitsLoop


/-! ## Incrementing the walk index -/

section Fields

variable {ns nr : ℕ} (cap : ℕ)

/-- Adding a carry to base-`2^kh` digits, lowest first: the new digits and the carry out. -/
def digitsInc (kh : ℕ) : List ℕ → Bool → List ℕ × Bool
  | [], c => ([], c)
  | d :: ds, c => ((d + c.toNat) % 2 ^ kh :: (digitsInc kh ds (decide (d + c.toNat = 2 ^ kh))).1,
      (digitsInc kh ds (decide (d + c.toNat = 2 ^ kh))).2)

/-- One field: skip its count, then add the carry to its bits. Registers: `Z 0` the carry, `Z 1` a counter,
`Z 2` scratch, `Z 3` the width `kh`. -/
def fieldStep (CT : Fin (ns + 1)) (Z : Fin 5 ↪ Fin nr) : WMX ns nr :=
  .seq (.wm (NearCubicGates.Close.Codec.dupR (Z 3) (Z 1) (Z 2)))
  (.seq (.wm (NearCubicGates.Close.Codec.skipLoop (Z 1) CT))
  (.seq (WMX.fwd CT)
  (.seq (.wm (NearCubicGates.Close.Codec.dupR (Z 3) (Z 1) (Z 2))) (bitsLoop CT (Z 0) (Z 1)))))

/-- The state during the increment: `Z 4` the fields left. -/
def fSt (σ : WState ns nr) (CT : Fin (ns + 1)) (Z : Fin 5 ↪ Fin nr) (content : List Bool) (h f c : ℕ) :
    WState ns nr :=
  bitsSt (σ.setv (Z 4) f) CT (Z 0) (Z 1) content h 0 c

theorem Z_ne (Z : Fin 5 ↪ Fin nr) {a b : Fin 5} (h : a ≠ b) : Z a ≠ Z b := Z.injective.ne h

theorem fSt_val (σ : WState ns nr) (CT : Fin (ns + 1)) (Z : Fin 5 ↪ Fin nr) (content : List Bool) (h f c : ℕ)
    (i : Fin 5) : (fSt σ CT Z content h f c).val (Z i) =
      if i = 0 then c else if i = 1 then 0 else if i = 4 then f else σ.val (Z i) := by
  unfold fSt bitsSt
  fin_cases i <;> simp [Function.update_apply, Z_ne Z (show (0 : Fin 5) ≠ 1 by decide),
    Z_ne Z (show (0 : Fin 5) ≠ 4 by decide), Z_ne Z (show (1 : Fin 5) ≠ 4 by decide),
    Z_ne Z (show (2 : Fin 5) ≠ 0 by decide), Z_ne Z (show (2 : Fin 5) ≠ 1 by decide),
    Z_ne Z (show (2 : Fin 5) ≠ 4 by decide), Z_ne Z (show (3 : Fin 5) ≠ 0 by decide),
    Z_ne Z (show (3 : Fin 5) ≠ 1 by decide), Z_ne Z (show (3 : Fin 5) ≠ 4 by decide),
    Z_ne Z (show (1 : Fin 5) ≠ 0 by decide), Z_ne Z (show (4 : Fin 5) ≠ 0 by decide),
    Z_ne Z (show (4 : Fin 5) ≠ 1 by decide)]

end Fields


section FieldStep

variable {ns nr : ℕ} (cap : ℕ)

theorem bitsSt_setU (σ : WState ns nr) (CT : Fin (ns + 1)) (CY U : Fin nr) (hCU : CY ≠ U) (content : List Bool)
    (h u u' c : ℕ) : (bitsSt σ CT CY U content h u c).setv U u' = bitsSt σ CT CY U content h u' c := by
  refine WState.eq rfl rfl ?_ rfl
  funext q; by_cases hq : q = U
  · subst hq; simp [bitsSt, Function.update_of_ne hCU.symm]
  · by_cases hq' : q = CY
    · subst hq'; simp [bitsSt, Function.update_of_ne hCU]
    · simp [bitsSt, Function.update_of_ne hq, Function.update_of_ne hq']

theorem bitsSt_seth (σ : WState ns nr) (CT : Fin (ns + 1)) (CY U : Fin nr) (content : List Bool) (h h' u c : ℕ) :
    (bitsSt σ CT CY U content h u c).seth CT h' = bitsSt σ CT CY U content h' u c := by
  refine WState.eq ?_ rfl rfl rfl
  funext q; by_cases hq : q = CT
  · subst hq; simp [bitsSt]
  · simp [bitsSt, Function.update_of_ne hq]

theorem bitsSt_val_U (σ : WState ns nr) (CT : Fin (ns + 1)) (CY U : Fin nr) (hCU : CY ≠ U) (content : List Bool)
    (h u c : ℕ) : (bitsSt σ CT CY U content h u c).val U = u := by
  simp [bitsSt, Function.update_of_ne hCU.symm]

theorem bitsSt_sh (σ : WState ns nr) (CT : Fin (ns + 1)) (CY U : Fin nr) (content : List Bool) (h u c : ℕ) :
    (bitsSt σ CT CY U content h u c).sh CT = h := by simp [bitsSt]

theorem bitsSt_val_other (σ : WState ns nr) (CT : Fin (ns + 1)) (CY U : Fin nr) (content : List Bool) (h u c : ℕ)
    (r : Fin nr) (hr1 : r ≠ CY) (hr2 : r ≠ U) : (bitsSt σ CT CY U content h u c).val r = σ.val r := by
  simp [bitsSt, Function.update_of_ne hr1, Function.update_of_ne hr2]

theorem countField_split (kh d : ℕ) (pre rest : List Bool) :
    pre ++ countField kh d ++ rest = (pre ++ List.replicate kh true ++ [false]) ++ binary kh d ++ rest := by
  simp [countField, List.append_assoc]

/-- **One field of the increment.** -/
theorem fieldStep_exec (CT : Fin (ns + 1)) (Z : Fin 5 ↪ Fin nr) (σ : WState ns nr) (kh : ℕ)
    (hKH : σ.val (Z 3) = kh) (hD : σ.val (Z 2) = 0) (pre rest : List Bool) (d : ℕ) (hd : d < 2 ^ kh) (f : ℕ)
    (c : Bool) (hcap : 2 * kh + 2 ≤ cap) :
    WXExec cap (fieldStep CT Z) (fSt σ CT Z (pre ++ countField kh d ++ rest) pre.length f c.toNat)
      (fSt σ CT Z (pre ++ countField kh ((d + c.toNat) % 2 ^ kh) ++ rest) (pre.length + (2 * kh + 1)) f
        (decide (d + c.toNat = 2 ^ kh)).toNat) (60 * kh + 20) := by
  have h01 := Z_ne Z (show (0 : Fin 5) ≠ 1 by decide)
  have h31 : Z 3 ≠ Z 1 := Z_ne Z (by decide)
  have h32 : Z 3 ≠ Z 2 := Z_ne Z (by decide)
  have h12 : Z 1 ≠ Z 2 := Z_ne Z (by decide)
  set σf := σ.setv (Z 4) f with hσf
  have hKHf : σf.val (Z 3) = kh := by simp [hσf, Z_ne Z (show (3 : Fin 5) ≠ 4 by decide), hKH]
  have hDf : σf.val (Z 2) = 0 := by simp [hσf, Z_ne Z (show (2 : Fin 5) ≠ 4 by decide), hD]
  set content := pre ++ countField kh d ++ rest with hcontent
  have vKH : ∀ h u cc, (bitsSt σf CT (Z 0) (Z 1) content h u cc).val (Z 3) = kh := fun h u cc => by
    rw [bitsSt_val_other _ _ _ _ _ _ _ _ _ (Z_ne Z (by decide)) h31]; exact hKHf
  have vD : ∀ h u cc, (bitsSt σf CT (Z 0) (Z 1) content h u cc).val (Z 2) = 0 := fun h u cc => by
    rw [bitsSt_val_other _ _ _ _ _ _ _ _ _ (Z_ne Z (by decide)) h12.symm]; exact hDf
  -- the width into the counter
  have e1 := NearCubicGates.Close.Codec.dupR_spec cap (Z 3) (Z 1) (Z 2) h31 h32 h12
    (bitsSt σf CT (Z 0) (Z 1) content pre.length 0 c.toNat) (vD _ _ _) (by rw [vKH, bitsSt_val_U _ _ _ _ h01]; omega)
  rw [vKH, bitsSt_val_U _ _ _ _ h01, Nat.zero_add, bitsSt_setU _ _ _ _ h01] at e1
  -- past the count
  have e2 := NearCubicGates.Close.Codec.skipLoop_spec cap (Z 1) CT kh
    (bitsSt σf CT (Z 0) (Z 1) content pre.length kh c.toNat) (bitsSt_val_U _ _ _ _ h01 _ _ _ _) (by omega)
  rw [bitsSt_setU _ _ _ _ h01, bitsSt_sh, bitsSt_seth] at e2
  have e3 := WXExec.fwd cap CT (bitsSt σf CT (Z 0) (Z 1) content (pre.length + kh) 0 c.toNat)
  rw [bitsSt_sh, bitsSt_seth] at e3
  have e4 := NearCubicGates.Close.Codec.dupR_spec cap (Z 3) (Z 1) (Z 2) h31 h32 h12
    (bitsSt σf CT (Z 0) (Z 1) content (pre.length + kh + 1) 0 c.toNat) (vD _ _ _)
    (by rw [vKH, bitsSt_val_U _ _ _ _ h01]; omega)
  rw [vKH, bitsSt_val_U _ _ _ _ h01, Nat.zero_add, bitsSt_setU _ _ _ _ h01] at e4
  -- the carry through the bits
  have e5 := bitsLoop_exec cap CT (Z 0) (Z 1) h01 σf rest (binary kh d) (pre ++ List.replicate kh true ++ [false]) c
    (by simp; omega) (by omega)
  have hpre : (pre ++ List.replicate kh true ++ [false]).length = pre.length + kh + 1 := by simp; omega
  rw [← countField_split, hpre,
    show (binary kh d).length = kh from NearCubicWires.RepairOrdinary.SignedSortKey.binary_length kh d,
    bitsInc_binary kh d hd c] at e5
  refine WXExec.mono (WXExec.cast cap (WXExec.seq (WXExec.wm e1) (WXExec.seq (WXExec.wm e2) (WXExec.seq e3
    (WXExec.seq (WXExec.wm e4) e5)))) ?_ le_rfl) (by omega)
  unfold fSt
  rw [← hσf, countField_split]
  congr 1
  omega

end FieldStep


section FieldsLoop

variable {ns nr : ℕ} (cap : ℕ)

/-- **The increment of the walk index**: add the carry `Z 0` through the next `Z 4` fields. -/
def fieldsLoop (CT : Fin (ns + 1)) (Z : Fin 5 ↪ Fin nr) : WMX ns nr :=
  .whr (Z 4) (.seq (WMX.dec (Z 4)) (fieldStep CT Z))

theorem countField_length (kh d : ℕ) : (countField kh d).length = 2 * kh + 1 := by
  simp [countField]; omega

theorem fSt_setF (σ : WState ns nr) (CT : Fin (ns + 1)) (Z : Fin 5 ↪ Fin nr) (content : List Bool) (h f f' c : ℕ) :
    (fSt σ CT Z content h f c).setv (Z 4) f' = fSt σ CT Z content h f' c := by
  refine WState.eq rfl rfl ?_ rfl
  funext q
  by_cases h4 : q = Z 4
  · subst h4
    simp [fSt, bitsSt, Z_ne Z (show (4 : Fin 5) ≠ 0 by decide), Z_ne Z (show (4 : Fin 5) ≠ 1 by decide)]
  · simp [fSt, bitsSt, Function.update_apply, h4]

theorem fieldsLoop_exec (CT : Fin (ns + 1)) (Z : Fin 5 ↪ Fin nr) (σ : WState ns nr) (kh : ℕ)
    (hKH : σ.val (Z 3) = kh) (hD : σ.val (Z 2) = 0) (rest : List Bool) (hcap : 2 * kh + 2 ≤ cap) :
    ∀ (ds : List ℕ) (pre : List Bool) (c : Bool), (∀ d ∈ ds, d < 2 ^ kh) → ds.length ≤ cap →
      WXExec cap (fieldsLoop CT Z) (fSt σ CT Z (pre ++ ds.flatMap (countField kh) ++ rest) pre.length ds.length c.toNat)
        (fSt σ CT Z (pre ++ (digitsInc kh ds c).1.flatMap (countField kh) ++ rest)
          (pre.length + ds.length * (2 * kh + 1)) 0 (digitsInc kh ds c).2.toNat) (ds.length * (60 * kh + 25) + 1)
  | [], pre, c, _, _ => by
    refine WXExec.cast cap (WXExec.whrF ?_) (by simp [digitsInc]) (by simp)
    rw [fSt_val]; simp
  | d :: ds, pre, c, hds, hlen => by
    have hc1 : pre ++ (d :: ds).flatMap (countField kh) ++ rest = pre ++ countField kh d ++
        (ds.flatMap (countField kh) ++ rest) := by simp [List.append_assoc]
    rw [hc1]
    have hF : (fSt σ CT Z (pre ++ countField kh d ++ (ds.flatMap (countField kh) ++ rest)) pre.length
        (d :: ds).length c.toNat).val (Z 4) = ds.length + 1 := by rw [fSt_val]; simp
    have e1 := WXExec.dec cap (Z 4) (fSt σ CT Z (pre ++ countField kh d ++ (ds.flatMap (countField kh) ++ rest))
      pre.length (d :: ds).length c.toNat) (by rw [hF]; simp at hlen; omega)
    rw [hF, Nat.add_sub_cancel, fSt_setF] at e1
    have e2 := fieldStep_exec cap CT Z σ kh hKH hD pre (ds.flatMap (countField kh) ++ rest) d (hds d (by simp))
      ds.length c hcap
    set d' := (d + c.toNat) % 2 ^ kh with hd'
    set c' := decide (d + c.toNat = 2 ^ kh) with hc'
    have hd'lt : d' < 2 ^ kh := Nat.mod_lt _ (by positivity)
    have e3 := fieldsLoop_exec CT Z σ kh hKH hD rest hcap ds (pre ++ countField kh d') c'
      (fun x hx => hds x (by simp [hx])) (by simp at hlen; omega)
    have hc2 : pre ++ countField kh d' ++ (ds.flatMap (countField kh) ++ rest) =
        (pre ++ countField kh d') ++ ds.flatMap (countField kh) ++ rest := by simp [List.append_assoc]
    have hlenpre : (pre ++ countField kh d').length = pre.length + (2 * kh + 1) := by
      rw [List.length_append, countField_length]
    rw [hc2, ← hlenpre] at e2
    refine WXExec.mono (WXExec.cast cap (WXExec.whrT (by rw [hF]; omega) (WXExec.seq e1 e2) e3) ?_ le_rfl) ?_
    · have hh : (pre ++ countField kh d').length + ds.length * (2 * kh + 1) =
          pre.length + (d :: ds).length * (2 * kh + 1) := by
        rw [hlenpre]; simp only [List.length_cons]; ring
      rw [hh]
      simp only [digitsInc, ← hd', ← hc', List.flatMap_cons, List.append_assoc]
    · simp; ring_nf; omega

end FieldsLoop


/-! ## The digits of the walk index -/

/-- The `m` base-`2^kh` digits of `i`, lowest first: slot `j` of the walk of index `i`. -/
def walkDigits (kh : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | m + 1, i => i % 2 ^ kh :: walkDigits kh m (i / 2 ^ kh)

theorem digitsInc_false (kh : ℕ) (ds : List ℕ) (hds : ∀ d ∈ ds, d < 2 ^ kh) : digitsInc kh ds false = (ds, false) := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    have hd := hds d (by simp)
    have h1 : decide (d + (false : Bool).toNat = 2 ^ kh) = false := by simp; omega
    simp only [digitsInc, h1, ih (fun x hx => hds x (by simp [hx]))]
    simp [Nat.mod_eq_of_lt hd]

theorem walkDigits_lt (kh m i : ℕ) : ∀ d ∈ walkDigits kh m i, d < 2 ^ kh := by
  induction m generalizing i with
  | zero => simp [walkDigits]
  | succ m ih =>
    intro d hd
    simp only [walkDigits, List.mem_cons] at hd
    rcases hd with rfl | hd
    · exact Nat.mod_lt _ (by positivity)
    · exact ih _ d hd

theorem walkDigits_length (kh m i : ℕ) : (walkDigits kh m i).length = m := by
  induction m generalizing i with
  | zero => rfl
  | succ m ih => simp [walkDigits, ih]

theorem digitsInc_cons_true (kh d : ℕ) (ds : List ℕ) :
    digitsInc kh (d :: ds) true = ((d + 1) % 2 ^ kh :: (digitsInc kh ds (decide (d + 1 = 2 ^ kh))).1,
      (digitsInc kh ds (decide (d + 1 = 2 ^ kh))).2) := rfl

/-- **The increment of the walk index**: adding the carry `1` to the digits of `i < 2^{kh·m}` gives the digits of
`i + 1`, with carry out exactly when `i + 1 = 2^{kh·m}`. -/
theorem digitsInc_walkDigits (kh : ℕ) : ∀ (m i : ℕ), i < 2 ^ (kh * m) →
    digitsInc kh (walkDigits kh m i) true = (walkDigits kh m (i + 1), decide (i + 1 = 2 ^ (kh * m)))
  | 0, i, hi => by
    have : i = 0 := by simpa using hi
    subst this; simp [walkDigits, digitsInc]
  | m + 1, i, hi => by
    have hP : 0 < 2 ^ kh := by positivity
    have hpow : 2 ^ (kh * (m + 1)) = 2 ^ kh * 2 ^ (kh * m) := by rw [mul_add, mul_one, pow_add, mul_comm]
    have hq : i / 2 ^ kh < 2 ^ (kh * m) := by
      rw [Nat.div_lt_iff_lt_mul hP]; rw [hpow] at hi; linarith [mul_comm (2 ^ kh) (2 ^ (kh * m))]
    have hr := Nat.mod_lt i hP
    have hdecomp := Nat.div_add_mod i (2 ^ kh)
    simp only [walkDigits]
    rw [digitsInc_cons_true]
    by_cases hc : i % 2 ^ kh + 1 = 2 ^ kh
    · -- the lowest digit overflows
      rw [show decide (i % 2 ^ kh + 1 = 2 ^ kh) = true from decide_eq_true hc,
        digitsInc_walkDigits kh m (i / 2 ^ kh) hq]
      have h1 : (i + 1) % 2 ^ kh = 0 := by
        have : i + 1 = 2 ^ kh * (i / 2 ^ kh + 1) := by rw [mul_add, mul_one]; omega
        rw [this]; simp
      have h2 : (i + 1) / 2 ^ kh = i / 2 ^ kh + 1 := by
        have : i + 1 = 2 ^ kh * (i / 2 ^ kh + 1) := by rw [mul_add, mul_one]; omega
        rw [this, Nat.mul_div_cancel_left _ hP]
      rw [hc, Nat.mod_self, h1, h2]
      simp only [Prod.mk.injEq, true_and]
      congr 1
      apply propext
      rw [hpow]
      constructor
      · intro h; rw [← h, mul_add, mul_one]; omega
      · intro h
        have : 2 ^ kh * (i / 2 ^ kh + 1) = 2 ^ kh * 2 ^ (kh * m) := by rw [mul_add, mul_one]; omega
        exact Nat.eq_of_mul_eq_mul_left hP this
    · -- no carry out of the lowest digit
      rw [show decide (i % 2 ^ kh + 1 = 2 ^ kh) = false from decide_eq_false hc,
        digitsInc_false kh _ (walkDigits_lt kh m _)]
      have hlt : i % 2 ^ kh + 1 < 2 ^ kh := by omega
      have h1 : (i + 1) % 2 ^ kh = i % 2 ^ kh + 1 := by
        have hi' : i + 1 = 2 ^ kh * (i / 2 ^ kh) + (i % 2 ^ kh + 1) := by omega
        rw [hi', Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
      have h2 : (i + 1) / 2 ^ kh = i / 2 ^ kh := by
        have : i + 1 = 2 ^ kh * (i / 2 ^ kh) + (i % 2 ^ kh + 1) := by omega
        rw [this, Nat.mul_add_div hP, Nat.div_eq_of_lt hlt, Nat.add_zero]
      rw [Nat.mod_eq_of_lt hlt, h1, h2]
      simp only [Prod.mk.injEq, true_and]
      symm
      simp only [decide_eq_false_iff_not]
      intro h
      rw [hpow] at h
      have : i + 1 ≤ 2 ^ kh * (i / 2 ^ kh) + 2 ^ kh - 1 := by omega
      have : 2 ^ kh * (i / 2 ^ kh) + 2 ^ kh ≤ 2 ^ kh * 2 ^ (kh * m) := by
        rw [← mul_add_one]; exact Nat.mul_le_mul_left _ (by omega)
      omega


/-- The digits of the walk index are the base-`N` digits of `finFunctionFinEquiv`, `N = 2^kh`: slot `j` of the walk
of index `i` (`Greedy.walkList`). -/
theorem walkDigits_eq (kh : ℕ) : ∀ (m i : ℕ),
    walkDigits kh m i = List.ofFn fun j : Fin m => i / (2 ^ kh) ^ (j : ℕ) % 2 ^ kh
  | 0, i => rfl
  | m + 1, i => by
    rw [walkDigits, walkDigits_eq kh m (i / 2 ^ kh), List.ofFn_succ]
    simp only [Fin.val_zero, pow_zero, Nat.div_one, Fin.val_succ, pow_succ', Nat.div_div_eq_div_mul]

/-! ## Naming a walk -/

section Emit

variable {ns nr : ℕ} (cap : ℕ)

/-- Write the slots of the walk: `Codec.numW` on each of `m` count fields, appending `marks (natWord d)`. -/
def emitSlots (CT o : Fin (ns + 1)) (Y : Fin 5 ↪ Fin nr) (OP : Fin nr) : ℕ → WM ns nr
  | 0 => .skip
  | m + 1 => .seq (NearCubicGates.Close.Codec.numW CT o Y OP) (emitSlots CT o Y OP m)

theorem readCount_replicate (X : List Bool) :
    ∀ k, NearCubicGates.Close.Worker.Format.readCount (List.replicate k true ++ false :: X) = (k, X)
  | 0 => by simp [NearCubicGates.Close.Worker.Format.readCount]
  | k + 1 => by
    simp only [List.replicate_succ, List.cons_append, NearCubicGates.Close.Worker.Format.readCount,
      readCount_replicate X k]

theorem ofFn_getD_prefix (l r : List Bool) (k : ℕ) (hk : l.length = k) :
    (List.ofFn fun i : Fin k => (l ++ r).getD i.val false) = l := by
  subst hk
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_ofFn]
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left]

/-- A count field reads back as its number. -/
theorem readNum_countField (kh d : ℕ) (hd : d < 2 ^ kh) (rest : List Bool) :
    NearCubicGates.Close.Worker.Format.readNum (countField kh d ++ rest) = (d, rest) := by
  have hc : NearCubicGates.Close.Worker.Format.readCount (countField kh d ++ rest) = (kh, binary kh d ++ rest) := by
    unfold countField
    rw [List.append_assoc, List.cons_append]
    exact readCount_replicate _ kh
  unfold NearCubicGates.Close.Worker.Format.readNum NearCubicGates.Close.Worker.Format.readField
    NearCubicGates.Close.Worker.Format.readBits
  rw [hc]
  simp only
  rw [ofFn_getD_prefix _ _ kh (NearCubicWires.RepairOrdinary.SignedSortKey.binary_length kh d),
    NearCubicWires.RepairOrdinary.SignedSortKey.binary_value kh d hd]
  simp

/-- The count of a count field is its width. -/
theorem fieldLen_countField (kh d : ℕ) (pre rest : List Bool) :
    NearCubicGates.Close.Codec.fieldLen (pre ++ countField kh d ++ rest) pre.length = kh := by
  unfold NearCubicGates.Close.Codec.fieldLen
  rw [List.append_assoc, List.drop_left]
  unfold countField
  rw [List.append_assoc, List.cons_append, readCount_replicate]


theorem natWord_length_le_field (kh d : ℕ) (hd : d < 2 ^ kh) : (natWord d).length ≤ 2 * kh + 3 := by
  rw [NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_length]
  have := natBitLength_le_of_lt_pow (E := kh + 1) (by omega)
    (lt_trans hd (Nat.pow_lt_pow_right (by norm_num) (by omega)))
  omega

theorem appendO_seth_comm (σ : WState ns nr) (o i : Fin (ns + 1)) (hio : i ≠ o) (OP : Fin nr) (u : List Bool) (x : ℕ) :
    (NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO σ o OP u).seth i x =
      NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO (σ.seth i x) o OP u := by
  refine WState.eq ?_ rfl rfl rfl
  funext q
  by_cases hq : q = i
  · subst hq; simp [NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO, Function.update_of_ne hio]
  · by_cases hq' : q = o
    · subst hq'; simp [NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO, Function.update_of_ne hio.symm]
    · simp [NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO, Function.update_of_ne hq,
        Function.update_of_ne hq']

/-- **Naming the walk**: on the count fields of the digits `ds` (head at their start), `emitSlots` appends
`marks (natWord d)` for each digit, in order, and moves the head past the fields. -/
theorem emitSlots_exec (CT o : Fin (ns + 1)) (Y : Fin 5 ↪ Fin nr) (OP : Fin nr) (hCo : CT ≠ o)
    (hOP : ∀ i, Y i ≠ OP) (kh : ℕ) (rest : List Bool) (hk : kh + 1 ≤ cap) :
    ∀ (ds : List ℕ) (pre : List Bool) (σ : WState ns nr), (∀ d ∈ ds, d < 2 ^ kh) →
      σ.st CT = pre ++ ds.flatMap (countField kh) ++ rest → σ.sh CT = pre.length → (∀ i, σ.val (Y i) = 0) →
      σ.sh o = (σ.st o).length → σ.val OP + (ds.length + 1) * (4 * kh + 8) ≤ cap →
      WExec cap (emitSlots CT o Y OP ds.length) σ
        (NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO (σ.seth CT (pre.length + ds.length * (2 * kh + 1)))
          o OP (marks (ds.flatMap natWord))) (ds.length * (3 * kh ^ 2 + 100 * kh + 81))
  | [], pre, σ, _, _, hsh, _, ho, _ => by
    simp only [List.length_nil, emitSlots, List.flatMap_nil, Nat.zero_mul, Nat.add_zero]
    refine WExec.cast cap (WExec.skip σ) ?_ le_rfl
    rw [show marks ([] : List Bool) = [] from rfl,
      NearCubicGates.Close.Codec.appendO_nil _ _ _ (by simp [Function.update_of_ne hCo.symm, ho])]
    refine WState.eq ?_ rfl rfl rfl
    funext q; by_cases hq : q = CT
    · subst hq; simp [hsh]
    · simp [Function.update_of_ne hq]
  | d :: ds, pre, σ, hds, hst, hsh, hY, ho, hc => by
    have hd := hds d (by simp)
    have hst' : σ.st CT = pre ++ countField kh d ++ (ds.flatMap (countField kh) ++ rest) := by
      rw [hst]; simp [List.append_assoc]
    have hfl : NearCubicGates.Close.Codec.fieldLen (σ.st CT) (σ.sh CT) = kh := by
      rw [hst', hsh]; exact fieldLen_countField kh d pre _
    have hrn : (NearCubicGates.Close.Worker.Format.readNum ((σ.st CT).drop (σ.sh CT))).1 = d := by
      rw [hst', hsh, List.append_assoc, List.drop_left, readNum_countField kh d hd]
    have e1 := NearCubicGates.Close.Codec.numW_spec cap CT o Y OP hCo hOP σ hY ho (by rw [hfl]; exact hk)
      (by rw [hfl]; simp at hc; nlinarith)
    rw [hfl, hrn] at e1
    set σ1 := NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO (σ.seth CT (σ.sh CT + kh + 1 + kh)) o OP
      (marks (natWord d)) with hσ1
    have hl := natWord_length_le_field kh d hd
    have e2 := emitSlots_exec CT o Y OP hCo hOP kh rest hk ds (pre ++ countField kh d) σ1
      (fun x hx => hds x (by simp [hx]))
      (by simp [hσ1, Function.update_of_ne hCo, hst', List.append_assoc])
      (by simp [hσ1, Function.update_of_ne hCo, hsh, countField_length]; omega)
      (fun i => by simp [hσ1, Function.update_of_ne (hOP i), hY i])
      (by simp [hσ1, Function.update_of_ne hCo.symm, ho])
      (by
        have e : ((d :: ds).length + 1) * (4 * kh + 8) = (ds.length + 1) * (4 * kh + 8) + (4 * kh + 8) := by
          simp only [List.length_cons]; ring
        simp only [hσ1, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO_val, Function.update_self,
          WState.seth_val, marks_length]
        omega)
    refine WExec.mono (WExec.cast cap (WExec.seq e1 e2) ?_ le_rfl) (by simp; nlinarith)
    rw [hσ1, appendO_seth_comm _ _ _ hCo, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO_append,
      seth_seth]
    have hx : (pre ++ countField kh d).length + ds.length * (2 * kh + 1) =
        pre.length + (d :: ds).length * (2 * kh + 1) := by
      simp only [List.length_append, countField_length, List.length_cons]; ring
    have hm : marks (natWord d) ++ marks (ds.flatMap natWord) = marks ((d :: ds).flatMap natWord) := by
      simp [marks_append]
    rw [hx, hm]

end Emit

end NearQuarticWires.Control
