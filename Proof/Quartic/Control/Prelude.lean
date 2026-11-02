import Proof.Quartic.Control.Head
import Proof.Quartic.Control.Parse

/-!
# The seed parameters of the coefficient requests

Paper: `cor:conditional`, paper/paper.tex, and `sec:params`: the coefficient
requests of a child evaluation carry `ℓ = ℓ_f`, `kh = k/2` and `Q` (`Cells.CoreRules.seedParameters`). On the word
after Step 2 (`Program.certWord`), `k` is the seventh parameter, `Q` the eighteenth and `ℓ_f` the nineteenth.

`seedHead` reads `k` (`readS` at the seventh number), halves it into a register, moves past ten numbers, copies
`natWord Q` aside on `T`, copies `natWord ℓ_f` to `HS`, writes `natWord kh` (`WriteNat.writeNatM`, imported from
`Proof.Wire_3_5`) and copies `natWord Q` back to `HS` (`seedHead_exec`).
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
  appendO_append appendO_setv writeNatM writeNatM_spec halveLoop halveLoop_spec)
open NearCubicWires.WireExponent3_5.PrimAsm.CopyNat (copyNatM copyNatM_spec)
open NearCubicGates.Close.Interfaces (Call)

/-! ## Registers -/

/-- The output counter of the stage word. -/
def rO : Fin lnr := ⟨27, by simp only [lnr]; omega⟩
/-- The read counter of the input copy. -/
def rI : Fin lnr := ⟨28, by simp only [lnr]; omega⟩
/-- The output counter of the fixed part of the requests. -/
def rH : Fin lnr := ⟨29, by simp only [lnr]; omega⟩
/-- The output counter of the table. -/
def rT : Fin lnr := ⟨30, by simp only [lnr]; omega⟩

/-- The registers of the parameter reader. -/
def cG : Fin 7 ↪ Fin lnr :=
  ⟨fun i => ⟨13 + i.val, by simp only [lnr]; omega⟩, fun a b h => Fin.ext (by have := congrArg Fin.val h; simp at this; omega)⟩

theorem cG_eq (i : Fin 7) : cG i = cR (Fin.castSucc i) := by
  apply Fin.ext; simp [cG, cR]

/-- The registers of the number writer: the value `v`, six scratch registers, the output counter `o`. -/
def natRegs (v o : Fin lnr) (hv : v.val < 13 ∨ 19 ≤ v.val) (ho : o.val < 13 ∨ 19 ≤ o.val) (hvo : v ≠ o) :
    Fin 8 ↪ Fin lnr where
  toFun i := if i.val = 0 then v else if i.val = 7 then o else ⟨12 + i.val, by have := i.isLt; simp only [lnr]; omega⟩
  inj' := by
    intro a b h
    have hv' := congrArg Fin.val h
    have hvo' : v.val ≠ o.val := fun e => hvo (Fin.ext e)
    apply Fin.ext
    have ha := a.isLt; have hb := b.isLt
    by_cases ha0 : a.val = 0 <;> by_cases hb0 : b.val = 0 <;> by_cases ha7 : a.val = 7 <;>
      by_cases hb7 : b.val = 7 <;> simp [ha0, hb0, ha7, hb7] at hv' <;> omega

theorem natRegs_zero (v o : Fin lnr) (hv : v.val < 13 ∨ 19 ≤ v.val) (ho : o.val < 13 ∨ 19 ≤ o.val) (hvo : v ≠ o) :
    natRegs v o hv ho hvo 0 = v := rfl

theorem natRegs_seven (v o : Fin lnr) (hv : v.val < 13 ∨ 19 ≤ v.val) (ho : o.val < 13 ∨ 19 ≤ o.val) (hvo : v ≠ o) :
    natRegs v o hv ho hvo 7 = o := rfl

theorem natRegs_mid (v o : Fin lnr) (hv : v.val < 13 ∨ 19 ≤ v.val) (ho : o.val < 13 ∨ 19 ≤ o.val) (hvo : v ≠ o)
    (i : Fin 8) (h0 : i.val ≠ 0) (h7 : i.val ≠ 7) : natRegs v o hv ho hvo i = cR ⟨i.val - 1, by omega⟩ := by
  have h0' : i ≠ 0 := fun e => h0 (by simp [e])
  have h7' : i ≠ 7 := fun e => h7 (by simp [e])
  apply Fin.ext
  simp [natRegs, h0, h7, h0', h7', cR]; omega

/-- The number writer for `kh` (in `cZ 3`) onto `HS`. -/
def khRegs : Fin 8 ↪ Fin lnr :=
  natRegs (cZ 3) rH (by right; simp [cZ]) (by right; simp [rH]) (by intro h; have := congrArg Fin.val h; simp [cZ, rH] at this)

/-- Two registers of the prelude differ (by their indices). -/
local macro "pdst" : tactic =>
  `(tactic| (intro hh; have hv := congrArg Fin.val hh; simp [cY, cR, cZ, cG, cOP, cC, cLC, cD, cNX, rS, rO, rI, rH,
    rT] at hv <;> omega))

/-! ## The seed parameters -/

/-- **The seed parameters onto `HS`**: `natWord ℓ ++ natWord kh ++ natWord Q`, `kh = k/2` into `cZ 3`. -/
def seedHead {ns : ℕ} (IN HS T : Fin (ns + 1)) : WM ns lnr :=
  .seq (readS IN cG 6)
  (.seq (halveLoop (cR 6) (cZ 3) (cR 7))
  (.seq (WM.clear (cR 7))
  (.seq (skipNats IN (cR 0) (cR 1) 10)
  (.seq (copyNatM true IN T (cR 0) (cR 1) (cY 0))
  (.seq (copyNatM true IN HS (cR 0) (cR 1) rH)
  (.seq (writeNatM HS khRegs)
  (.seq (NearCubicGates.Close.Codec.rewindLoop T (cY 0))
  (copyNatM true T HS (cR 0) (cR 1) rH))))))))

/-- The cost of `seedHead`. -/
def seedHeadCost (c : Call) (xs ys : List ℕ) (k Q ell : ℕ) : ℕ :=
  readCost c xs k + 1 + (5 * k + 4 + 1 + (4 + 1 + (natsCost ys + 1 + (60 * (natWord Q).length + 60 + 1 +
    (60 * (natWord ell).length + 60 + 1 + ((natBitLength (k / 2) + 10) * (100 * (k / 2) + 200) + 1 +
    (5 * (2 * (natWord Q).length) + 1 + 1 + (60 * (natWord Q).length + 60))))))))

/-- The fixed part of the requests before the prefix. -/
def seedWord (ell kh Q : ℕ) : List Bool := natWord ell ++ natWord kh ++ natWord Q

/-- The input before the seed parameters are read: the tag, the call word, the parameters up to `ℓ_f`. -/
def seedPre (c : Call) (xs : List ℕ) (k : ℕ) (ys : List ℕ) (Q ell : ℕ) : List Bool :=
  [true] ++ NearCubicGates.Close.Interfaces.callWord c ++ xs.flatMap natWord ++ natWord k ++ ys.flatMap natWord ++
    natWord Q ++ natWord ell

section SeedHead

variable {ns : ℕ} (cap : ℕ) (IN HS T : Fin (ns + 1))

/-- **Reading the seed parameters.** From the head at the start of the input word
`[true] ++ callWord c ++ natWords xs ++ natWord k ++ natWords ys ++ natWord Q ++ natWord ℓ ++ rest` (six numbers
`xs`, ten numbers `ys`), with `HS` and `T` empty: `HS` holds `marks (natWord ℓ ++ natWord kh ++ natWord Q)`, `T`
holds `marks (natWord Q)` (both heads at the end), `cZ 3 = k/2`, the input head is past `natWord ℓ`. -/
theorem seedHead_exec (hIH : IN ≠ HS) (hIT : IN ≠ T) (hHT : HS ≠ T) (σ : WState ns lnr) (c : Call) (xs ys : List ℕ)
    (k Q ell : ℕ) (rest restIN : List Bool)
    (hIN : σ.st IN = marks (seedPre c xs k ys Q ell ++ rest) ++ restIN) (hINh : σ.sh IN = 0)
    (hHS : σ.st HS = []) (hHSh : σ.sh HS = 0) (hT : σ.st T = []) (hTh : σ.sh T = 0)
    (hR : ∀ i, σ.val (cR i) = 0) (hY : σ.val (cY 0) = 0) (hZ : σ.val (cZ 3) = 0) (hH : σ.val rH = 0)
    (hfit : ReadFits cap c xs k) (hxs : xs.length = 6) (hys : ys.length = 10)
    (hyfit : ∀ y ∈ ys, natBitLength y + 1 ≤ cap)
    (hcap : 4 * (seedWord ell (k / 2) Q).length + k + 6 * natBitLength k + 20 ≤ cap) :
    WExec cap (seedHead IN HS T) σ
      ((((appendO (appendO σ T (cY 0) (marks (natWord Q))) HS rH (marks (seedWord ell (k / 2) Q))).seth IN
        (marks (seedPre c xs k ys Q ell)).length).setv (cY 0) 0).setv (cZ 3) (k / 2))
      (seedHeadCost c xs ys k Q ell) := by
  have hG : ∀ i, σ.val (cG i) = 0 := fun i => by rw [cG_eq]; exact hR _
  -- `k`
  have e1 := readS_exec cap σ IN cG c xs k (ys.flatMap natWord ++ natWord Q ++ natWord ell ++ rest) restIN
    (by rw [hIN]; unfold seedPre; simp only [List.append_assoc]) hINh hG hfit hxs
  set p1 := (marks ([true] ++ NearCubicGates.Close.Interfaces.callWord c ++ xs.flatMap natWord ++ natWord k)).length
    with hp1
  set σ1 := (σ.seth IN p1).setv (cG 6) k with hσ1
  have hc6 : cG 6 = cR 6 := by rw [cG_eq]; rfl
  rw [hc6] at hσ1
  have e2 := halveLoop_spec cap (cR 6) (cZ 3) (cR 7) (by pdst) (by pdst) (by pdst) k σ1
    (by simp [hσ1]) (by simp [hσ1, Function.update_of_ne (show cR 7 ≠ cR 6 by pdst), hR])
    (by have := hfit.rounds; have := Nat.lt_two_pow_self (n := k); have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) k
        simp only [natBitLength] at *; omega)
    (by simp [hσ1, Function.update_of_ne (show cZ 3 ≠ cR 6 by pdst), hZ]; omega) (by omega)
  set σ2 := ((σ1.setv (cR 6) 0).setv (cZ 3) (σ1.val (cZ 3) + k / 2)).setv (cR 7) (k % 2) with hσ2
  have e3 := wclear_spec cap (cR 7) (k % 2) σ2 (by simp [hσ2]) (by simp [hσ2]; omega)
  set σ3 := σ2.setv (cR 7) 0 with hσ3
  -- ten numbers
  have h3IN : σ3.st IN = marks ([true] ++ NearCubicGates.Close.Interfaces.callWord c ++ xs.flatMap natWord ++
      natWord k) ++ marks (ys.flatMap natWord) ++ (marks (natWord Q ++ natWord ell ++ rest) ++ restIN) := by
    simp only [hσ3, hσ2, hσ1, WState.setv_st, WState.seth_st, hIN, seedPre, marks_append, List.append_assoc]
  have e4 := skipNats_exec cap IN (cR 0) (cR 1) (by pdst) ys _ _ σ3 h3IN (by simp [hσ3, hσ2, hσ1, hp1])
    (by simp [hσ3, hσ2, hσ1, Function.update_apply, hR]; intro h1; have := congrArg Fin.val h1; simp [cR, cZ] at this)
    (by simp [hσ3, hσ2, hσ1, Function.update_apply, hR]; intro h1; have := congrArg Fin.val h1; simp [cR, cZ] at this)
    hyfit
  rw [hys] at e4
  set A2 := [true] ++ NearCubicGates.Close.Interfaces.callWord c ++ xs.flatMap natWord ++ natWord k ++
    ys.flatMap natWord with hA2
  have hp2 : p1 + 2 * (ys.flatMap natWord).length = (marks A2).length := by
    simp [hp1, hA2, marks_length]; ring
  rw [show (marks ([true] ++ NearCubicGates.Close.Interfaces.callWord c ++ xs.flatMap natWord ++
    natWord k)).length = p1 from rfl, hp2] at e4
  set σ4 := σ3.seth IN (marks A2).length with hσ4
  have hlenQ := NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_length Q
  have hlenE := NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_length ell
  have hlenK := NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_length (k / 2)
  have hsw : (seedWord ell (k / 2) Q).length = (natWord ell).length + (natWord (k / 2)).length +
      (natWord Q).length := by simp only [seedWord, List.length_append]
  have hRv : ∀ i, σ4.val (cR i) = 0 := by
    intro i
    have hz : cR i ≠ cZ 3 := by
      intro hh; have hv := congrArg Fin.val hh; have := i.isLt; simp [cR, cZ] at hv; omega
    by_cases h7 : cR i = cR 7
    · rw [h7]; simp [hσ4, hσ3]
    · by_cases h6 : cR i = cR 6
      · rw [h6]
        simp [hσ4, hσ3, hσ2, Function.update_of_ne (show cR 6 ≠ cR 7 by pdst),
          Function.update_of_ne (show cR 6 ≠ cZ 3 by pdst)]
      · simp [hσ4, hσ3, hσ2, hσ1, Function.update_of_ne h7, Function.update_of_ne h6, Function.update_of_ne hz, hR]
  have hY4 : σ4.val (cY 0) = 0 := by
    simp [hσ4, hσ3, hσ2, hσ1, Function.update_of_ne (show cY 0 ≠ cR 7 by pdst),
      Function.update_of_ne (show cY 0 ≠ cZ 3 by pdst), Function.update_of_ne (show cY 0 ≠ cR 6 by pdst), hY]
  have hH4 : σ4.val rH = 0 := by
    simp [hσ4, hσ3, hσ2, hσ1, Function.update_of_ne (show rH ≠ cR 7 by pdst),
      Function.update_of_ne (show rH ≠ cZ 3 by pdst), Function.update_of_ne (show rH ≠ cR 6 by pdst), hH]
  have hZ4 : σ4.val (cZ 3) = k / 2 := by
    simp [hσ4, hσ3, hσ2, hσ1, Function.update_of_ne (show cZ 3 ≠ cR 7 by pdst),
      Function.update_of_ne (show cZ 3 ≠ cR 6 by pdst), hZ]
  have h4IN : σ4.st IN = marks A2 ++ NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.enc true (natWord Q) ++
      (marks (natWord ell ++ rest) ++ restIN) := by
    simp only [hσ4, hσ3, hσ2, hσ1, WState.setv_st, WState.seth_st, hIN, seedPre, hA2, marks_append,
      List.append_assoc, enc_true]
  have h4T : σ4.st T = [] := by simp [hσ4, hσ3, hσ2, hσ1, hT]
  have h4Th : σ4.sh T = 0 := by simp [hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hIT.symm, hTh]
  have h4HS : σ4.st HS = [] := by simp [hσ4, hσ3, hσ2, hσ1, hHS]
  have h4HSh : σ4.sh HS = 0 := by simp [hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hIH.symm, hHSh]
  -- `Q` aside
  have e5 := copyNatM_spec cap true IN T hIT (cR 0) (cR 1) (cY 0) (by pdst) (by pdst) (by pdst) Q (marks A2) _ σ4
    h4IN (by simp [hσ4]) (by rw [h4T, h4Th]; rfl) (hRv 0) (hRv 1) (by rw [hY4]; omega)
  set σ5 := (appendO σ4 T (cY 0) (marks (natWord Q))).seth IN
    ((marks A2).length + NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.stp true * (natWord Q).length) with hσ5
  have h5IN : σ5.st IN = marks (A2 ++ natWord Q) ++ NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.enc true
      (natWord ell) ++ (marks rest ++ restIN) := by
    simp only [hσ5, WState.seth_st, appendO_st, Function.update_of_ne hIT, h4IN, marks_append, List.append_assoc,
      enc_true]
  -- `ℓ`
  have e6 := copyNatM_spec cap true IN HS hIH (cR 0) (cR 1) rH (by pdst) (by pdst) (by pdst) ell
    (marks (A2 ++ natWord Q)) _ σ5 h5IN
    (by simp only [hσ5, WState.seth_sh, Function.update_self, marks_length, List.length_append,
      NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.stp, ↓reduceIte]; ring)
    (by simp [hσ5, Function.update_of_ne hHT, Function.update_of_ne hIH.symm, h4HS, h4HSh])
    (by simp [hσ5, Function.update_of_ne (show cR 0 ≠ cY 0 by pdst), hRv 0])
    (by simp [hσ5, Function.update_of_ne (show cR 1 ≠ cY 0 by pdst), hRv 1])
    (by simp [hσ5, Function.update_of_ne (show rH ≠ cY 0 by pdst), hH4]; omega)
  set σ6 := (appendO σ5 HS rH (marks (natWord ell))).seth IN
    ((marks (A2 ++ natWord Q)).length + NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.stp true *
      (natWord ell).length) with hσ6
  have h6R : ∀ i : Fin 8, i.val ≠ 0 → i.val ≠ 7 → σ6.val (khRegs i) = 0 := by
    intro i h0 h7
    rw [khRegs, natRegs_mid _ _ _ _ _ i h0 h7]
    simp [hσ6, hσ5, Function.update_of_ne (show cR ⟨i.val - 1, by omega⟩ ≠ rH by pdst),
      Function.update_of_ne (show cR ⟨i.val - 1, by omega⟩ ≠ cY 0 by pdst), hRv]
  have h6Z : σ6.val (cZ 3) = k / 2 := by
    simp [hσ6, hσ5, Function.update_of_ne (show cZ 3 ≠ rH by pdst), Function.update_of_ne (show cZ 3 ≠ cY 0 by pdst),
      hZ4]
  have h6H : σ6.val rH = (marks (natWord ell)).length := by
    simp [hσ6, hσ5, Function.update_of_ne (show rH ≠ cY 0 by pdst), hH4]
  -- `kh`
  have e7 := writeNatM_spec cap HS khRegs σ6 (h6R 1 (by decide) (by decide)) (h6R 2 (by decide) (by decide))
    (h6R 3 (by decide) (by decide)) (h6R 4 (by decide) (by decide)) (h6R 5 (by decide) (by decide))
    (h6R 6 (by decide) (by decide))
    (by simp [hσ6, hσ5, Function.update_of_ne hIH.symm, Function.update_of_ne hHT, h4HS, h4HSh])
    (by
      rw [show khRegs 0 = cZ 3 from rfl, show khRegs 7 = rH from rfl, h6Z, h6H, marks_length]
      have := natBitLength_mono (show k / 2 ≤ k by omega); omega)
  rw [show khRegs 0 = cZ 3 from rfl, show khRegs 7 = rH from rfl, h6Z] at e7
  set σ7 := appendO σ6 HS rH (marks (natWord (k / 2))) with hσ7
  -- `Q` back
  have h7Y : σ7.val (cY 0) = 2 * (natWord Q).length := by
    simp [hσ7, hσ6, hσ5, Function.update_of_ne (show cY 0 ≠ rH by pdst), hY4, marks_length]
  have h7Th : σ7.sh T = 2 * (natWord Q).length := by
    simp [hσ7, hσ6, hσ5, Function.update_of_ne hHT.symm, Function.update_of_ne hIT.symm, h4T, h4Th, marks_length]
  have e8 := NearCubicGates.Close.Codec.rewindLoop_spec cap T (cY 0) (2 * (natWord Q).length) σ7 h7Y (by omega)
    (by omega)
  rw [h7Th, Nat.sub_self] at e8
  set σ8 := (σ7.setv (cY 0) 0).seth T 0 with hσ8
  have e9 := copyNatM_spec cap true T HS hHT.symm (cR 0) (cR 1) rH (by pdst) (by pdst) (by pdst) Q [] [] σ8
    (by simp [hσ8, hσ7, hσ6, hσ5, Function.update_of_ne hHT.symm, Function.update_of_ne hIT.symm, h4T, enc_true])
    (by simp [hσ8])
    (by simp [hσ8, hσ7, hσ6, hσ5, Function.update_of_ne hHT, Function.update_of_ne hIH.symm, h4HS, h4HSh])
    (by simp [hσ8, hσ7, hσ6, hσ5, Function.update_of_ne (show cR 0 ≠ cY 0 by pdst),
      Function.update_of_ne (show cR 0 ≠ rH by pdst), hRv 0])
    (by simp [hσ8, hσ7, hσ6, hσ5, Function.update_of_ne (show cR 1 ≠ cY 0 by pdst),
      Function.update_of_ne (show cR 1 ≠ rH by pdst), hRv 1])
    (by simp [hσ8, hσ7, hσ6, hσ5, Function.update_of_ne (show rH ≠ cY 0 by pdst), hH4, marks_length]; omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6
    (WExec.seq e7 (WExec.seq e8 e9)))))))) ?_ ?_
  · have hne1 : cZ 3 ≠ cY 0 := by pdst
    have hne2 : cZ 3 ≠ rH := by pdst
    have hne3 : cY 0 ≠ rH := by pdst
    have hne4 : cR 6 ≠ cZ 3 := by pdst
    have hne5 : cR 7 ≠ cZ 3 := by pdst
    have hne6 : cR 6 ≠ cR 7 := by pdst
    have hne7 : cR 6 ≠ cY 0 := by pdst
    have hne8 : cR 7 ≠ cY 0 := by pdst
    have hne9 : cR 6 ≠ rH := by pdst
    have hne10 : cR 7 ≠ rH := by pdst
    have hposA : (marks (seedPre c xs k ys Q ell)).length =
        (marks (A2 ++ natWord Q)).length + NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.stp true *
          (natWord ell).length := by
      simp [seedPre, hA2, marks_length, NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.stp]; ring
    refine WState.eq ?_ ?_ ?_ ?_
    · funext j
      by_cases jH : j = HS
      · subst jH
        simp [hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hHT, Function.update_of_ne hIH.symm,
          seedWord, marks_length]; omega
      · by_cases jT : j = T
        · subst jT
          simp [hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hHT.symm, Function.update_of_ne hIT.symm,
            hTh, marks_length, NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.stp]
        · by_cases jI : j = IN
          · subst jI
            simp [hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hIH, Function.update_of_ne hIT, hposA]
          · simp [hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_of_ne jH, Function.update_of_ne jT,
              Function.update_of_ne jI]
    · funext j
      by_cases jH : j = HS
      · subst jH
        simp [hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hHT, Function.update_of_ne hIH.symm,
          seedWord, marks_append, List.append_assoc]
      · by_cases jT : j = T
        · subst jT
          simp [hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hHT.symm, Function.update_of_ne jH,
            hT, enc_true]
        · simp [hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_of_ne jH, Function.update_of_ne jT]
    · funext r
      by_cases rZ : r = cZ 3
      · subst rZ
        simp [hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hne1, Function.update_of_ne hne2,
          Function.update_of_ne hne4.symm, Function.update_of_ne hne5.symm, hZ]
      · by_cases rY : r = cY 0
        · subst rY
          simp [hσ8, Function.update_of_ne hne1.symm, Function.update_of_ne hne3]
        · by_cases rh : r = rH
          · subst rh
            simp [hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hne2.symm,
              Function.update_of_ne hne3.symm, Function.update_of_ne hne9.symm, Function.update_of_ne hne10.symm,
              hH, seedWord, marks_length]; ring
          · by_cases r6 : r = cR 6
            · subst r6
              simp [hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hne4, Function.update_of_ne hne7,
                Function.update_of_ne hne9, Function.update_of_ne hne6, hR]
            · by_cases r7 : r = cR 7
              · subst r7
                simp [hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hne5, Function.update_of_ne hne8,
                  Function.update_of_ne hne10, hR]
              · simp [hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_of_ne rZ, Function.update_of_ne rY,
                  Function.update_of_ne rh, Function.update_of_ne r6, Function.update_of_ne r7]
    · simp [hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1]
  · unfold seedHeadCost
    have : k % 2 ≤ 1 := by omega
    simp only [NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.stp] at *
    omega

end SeedHead

end NearQuarticWires.Control
