import Proof.Quartic.Control.Prelude

/-!
# The prefix of the coefficient requests

Paper: `cor:conditional`, paper/paper.tex: a coefficient request carries the prefix `π` as its
length `|π|` and its number `prefixValue π` (`Greedy.gammaRequest`). On the child input
`certWord ++ frame π` (`Greedy.childInput`), the parameter word ends with eighteen numbers after `ℓ_f`, the list of
primes, nine numbers and the list of factors (`StageLift.parametersWord_block_layout`), followed by the framed
witness prefix and the framed certified bits.

* `tailSkip`, `tailSkip_exec`: move past the rest of the parameters and the two frames;
* `prefixHead`, `prefixHead_exec`: one scan of `frame π` writes `1^{|π|}` on `T` and counts `|π|` (written as
  `natWord |π|` on `HS`), a second scan writes `0 π`; the count field `1^{|π|} 0 π` is transcoded by `Codec.numW`
  into `natWord (prefixValue π)` on `HS`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearQuarticWires.Control

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.RepairOrdinary.Streaming (marks marks_length marks_append)
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat (appendO appendO_st appendO_sh appendO_val appendO_cell
  appendO_append appendO_setv writeNatM writeNatM_spec)
open NearCubicGates.Close.Interfaces (listWord)

/-- Two registers of the prelude differ (by their indices). -/
local macro "pdst" : tactic =>
  `(tactic| (intro hh; have hv := congrArg Fin.val hh; simp [cY, cR, cZ, cG, cOP, cC, cLC, cD, cNX, rS, rO, rI, rH,
    rT] at hv <;> omega))

/-! ## The rest of the parameters and the two frames -/

/-- Move past one list of numbers. -/
def skipNatList {ns : ℕ} (IN : Fin (ns + 1)) : WM ns lnr :=
  NearCubicGates.Close.Codec.skipList true IN (cR 0) (cR 1) (cR 2) (cR 4) (cR 5)
    (NearCubicGates.Close.Codec.skipNat true IN (cR 0) (cR 1))

/-- The cost of moving past one list of numbers. -/
def natListCost (xs : List ℕ) : ℕ :=
  NearCubicGates.Close.Codec.skipListCost xs.length (xs.map fun x => 20 * natBitLength x + 20)

/-- The capacity holds one list of numbers. -/
structure ListFits (cap : ℕ) (xs : List ℕ) : Prop where
  len2 : 2 ^ (natBitLength xs.length + 1) ≤ cap
  len : xs.length ≤ cap
  elems : ∀ x ∈ xs, natBitLength x + 1 ≤ cap

theorem skipNatList_exec {ns : ℕ} (cap : ℕ) (IN : Fin (ns + 1)) (xs : List ℕ) (hfit : ListFits cap xs)
    (pre rest : List Bool) (σ : WState ns lnr) (hst : σ.st IN = pre ++ marks (listWord natWord xs) ++ rest)
    (hsh : σ.sh IN = pre.length) (hR : ∀ i, σ.val (cR i) = 0) :
    WExec cap (skipNatList IN) σ (σ.seth IN (pre.length + (marks (listWord natWord xs)).length)) (natListCost xs) := by
  have hne : ∀ {a b : Fin 8}, a ≠ b → cR a ≠ cR b := fun h => cR.injective.ne h
  have hd5 : [cR 0, cR 1, cR 2, cR 4, cR 5].Nodup := by simp
  have := NearCubicGates.Close.Codec.skipList_spec cap true IN (cR 0) (cR 1) (cR 2) (cR 4) (cR 5)
    (NearCubicGates.Close.Codec.skipNat true IN (cR 0) (cR 1)) hd5 natWord
    (fun x => 20 * natBitLength x + 20) (fun τ => τ.val (cR 0) = 0 ∧ τ.val (cR 1) = 0)
    (fun τ x h => h) (fun τ x h => ⟨by simp [Function.update_of_ne (hne (show (0 : Fin 8) ≠ 2 by decide)), h.1],
      by simp [Function.update_of_ne (hne (show (1 : Fin 8) ≠ 2 by decide)), h.2]⟩) xs
    (fun x hx pre rest' τ hτ hst hsh => NearCubicGates.Close.Codec.skipNat_spec cap true IN (cR 0) (cR 1)
      (hne (by decide)) x pre rest' τ hst hsh hτ.1 hτ.2 (hfit.elems x hx))
    pre rest σ ⟨hR 0, hR 1⟩ (by rw [hst, enc_true]) hsh (hR 0) (hR 1) (hR 2) (hR 4) (hR 5) hfit.len2 hfit.len
  refine WExec.cast cap this ?_ le_rfl
  congr 1; simp [marks_length, NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.stp]

/-- **The rest of the parameters and the two frames.** -/
def tailSkip {ns : ℕ} (IN : Fin (ns + 1)) : WM ns lnr :=
  .seq (skipNats IN (cR 0) (cR 1) 18)
  (.seq (skipNatList IN)
  (.seq (skipNats IN (cR 0) (cR 1) 9)
  (.seq (skipNatList IN)
  (.seq (frameScan IN .skip) (frameScan IN .skip)))))

/-- The words moved past by `tailSkip`. -/
def tailWord (zs ps ws fs : List ℕ) (wp cb : List Bool) : List Bool :=
  zs.flatMap natWord ++ listWord natWord ps ++ ws.flatMap natWord ++ listWord natWord fs ++ frame wp ++ frame cb

/-- The cost of `tailSkip`. -/
def tailCost (zs ps ws fs : List ℕ) (wp cb : List Bool) : ℕ :=
  natsCost zs + 1 + (natListCost ps + 1 + (natsCost ws + 1 + (natListCost fs + 1 +
    (10 * wp.length + 5 + 1 + (10 * cb.length + 5)))))

theorem tailSkip_exec {ns : ℕ} (cap : ℕ) (IN : Fin (ns + 1)) (zs ps ws fs : List ℕ) (wp cb : List Bool)
    (hzs : zs.length = 18) (hws : ws.length = 9) (hzf : ∀ x ∈ zs, natBitLength x + 1 ≤ cap)
    (hwf : ∀ x ∈ ws, natBitLength x + 1 ≤ cap) (hpf : ListFits cap ps) (hff : ListFits cap fs)
    (pre rest : List Bool) (σ : WState ns lnr) (hst : σ.st IN = pre ++ marks (tailWord zs ps ws fs wp cb) ++ rest)
    (hsh : σ.sh IN = pre.length) (hR : ∀ i, σ.val (cR i) = 0) :
    WExec cap (tailSkip IN) σ (σ.seth IN (pre.length + (marks (tailWord zs ps ws fs wp cb)).length))
      (tailCost zs ps ws fs wp cb) := by
  have hR' : ∀ x i, (σ.seth IN x).val (cR i) = 0 := fun x i => by simp [hR]
  have hst' : ∀ x, (σ.seth IN x).st IN = σ.st IN := fun x => by simp
  set u1 := zs.flatMap natWord
  set u2 := listWord natWord ps
  set u3 := ws.flatMap natWord
  set u4 := listWord natWord fs
  have hT : tailWord zs ps ws fs wp cb = u1 ++ u2 ++ u3 ++ u4 ++ frame wp ++ frame cb := rfl
  have e1 := skipNats_exec cap IN (cR 0) (cR 1) (by pdst) zs pre
    (marks (u2 ++ u3 ++ u4 ++ frame wp ++ frame cb) ++ rest) σ
    (by rw [hst, hT]; simp only [marks_append, List.append_assoc] <;> rfl) hsh (hR 0) (hR 1) hzf
  rw [hzs] at e1
  have p1 : pre.length + 2 * u1.length = (pre ++ marks u1).length := by
    simp only [List.length_append, marks_length]
  rw [p1] at e1
  have e2 := skipNatList_exec cap IN ps hpf (pre ++ marks u1) (marks (u3 ++ u4 ++ frame wp ++ frame cb) ++ rest)
    (σ.seth IN (pre ++ marks u1).length)
    (by rw [hst', hst, hT]; simp only [marks_append, List.append_assoc] <;> rfl) (by simp) (hR' _)
  rw [seth_seth, show (pre ++ marks u1).length + (marks u2).length = (pre ++ marks u1 ++ marks u2).length by
    simp only [List.length_append]]
    at e2
  have e3 := skipNats_exec cap IN (cR 0) (cR 1) (by pdst) ws (pre ++ marks u1 ++ marks u2)
    (marks (u4 ++ frame wp ++ frame cb) ++ rest) (σ.seth IN (pre ++ marks u1 ++ marks u2).length)
    (by rw [hst', hst, hT]; simp only [marks_append, List.append_assoc] <;> rfl) (by simp) (hR' _ 0) (hR' _ 1) hwf
  rw [hws, seth_seth,
    show (pre ++ marks u1 ++ marks u2).length + 2 * u3.length = (pre ++ marks u1 ++ marks u2 ++ marks u3).length by
      simp only [List.length_append, marks_length]] at e3
  have e4 := skipNatList_exec cap IN fs hff (pre ++ marks u1 ++ marks u2 ++ marks u3)
    (marks (frame wp ++ frame cb) ++ rest) (σ.seth IN (pre ++ marks u1 ++ marks u2 ++ marks u3).length)
    (by rw [hst', hst, hT]; simp only [marks_append, List.append_assoc] <;> rfl) (by simp) (hR' _)
  rw [seth_seth, show (pre ++ marks u1 ++ marks u2 ++ marks u3).length + (marks u4).length =
    (pre ++ marks u1 ++ marks u2 ++ marks u3 ++ marks u4).length by simp only [List.length_append]] at e4
  have e5 := skipFrame_exec cap IN wp (pre ++ marks u1 ++ marks u2 ++ marks u3 ++ marks u4)
    (marks (frame cb) ++ rest) (σ.seth IN (pre ++ marks u1 ++ marks u2 ++ marks u3 ++ marks u4).length)
    (by rw [hst', hst, hT]; simp only [marks_append, List.append_assoc] <;> rfl) (by simp)
  rw [seth_seth, show (pre ++ marks u1 ++ marks u2 ++ marks u3 ++ marks u4).length + (marks (frame wp)).length =
    (pre ++ marks u1 ++ marks u2 ++ marks u3 ++ marks u4 ++ marks (frame wp)).length by simp only [List.length_append]] at e5
  have e6 := skipFrame_exec cap IN cb (pre ++ marks u1 ++ marks u2 ++ marks u3 ++ marks u4 ++ marks (frame wp))
    rest (σ.seth IN (pre ++ marks u1 ++ marks u2 ++ marks u3 ++ marks u4 ++ marks (frame wp)).length)
    (by rw [hst', hst, hT]; simp only [marks_append, List.append_assoc] <;> rfl) (by simp)
  rw [seth_seth] at e6
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 e6))))) ?_ ?_
  · congr 1; rw [hT]; simp only [marks_append, List.length_append]; omega
  · unfold tailCost; omega


/-! ## The prefix -/

/-- The number writer for `|π|` (in `cY 1`) onto `HS`. -/
def piRegs : Fin 8 ↪ Fin lnr :=
  natRegs (cY 1) rH (by left; simp [cY]) (by right; simp [rH]) (by pdst)

/-- **The prefix onto `HS`**: `natWord |π| ++ natWord (prefixValue π)`, through the count field `1^{|π|} 0 π`
written on `T`. -/
def prefixHead {ns : ℕ} (IN HS T : Fin (ns + 1)) : WM ns lnr :=
  .seq (frameScan IN (onesP T (cY 1) (cY 2)))
  (.seq (writeNatM HS piRegs)
  (.seq (NearCubicGates.Close.Codec.rewindLoop IN (cY 2))
  (.seq (.bwd IN) (.seq (.bwd IN)
  (.seq (emitC T (cY 1) false)
  (.seq (frameScan IN (bitP IN T (cY 1)))
  (.seq (NearCubicGates.Close.Codec.rewindLoop T (cY 1))
  (NearCubicGates.Close.Codec.numW T HS cY rH))))))))

/-- The cost of `prefixHead` for a prefix of length `L`. -/
def prefixCost (L : ℕ) : ℕ :=
  33 * L + 1 + 4 + 1 + ((natBitLength L + 10) * (100 * L + 200) + 1 + (5 * (4 * L) + 1 + 1 + (1 + 1 + (1 + 1 +
    (7 + 1 + (18 * L + 1 + 4 + 1 + (5 * (L + 1 + L) + 1 + 1 + (3 * L ^ 2 + 100 * L + 80))))))))

section PrefixHead

variable {ns : ℕ} (cap : ℕ) (IN HS T : Fin (ns + 1))

/-- **The prefix of the requests.** From the head at the start of `frame π` on the input, with `T` and `HS` heads at
their ends: `HS` gains `marks (natWord |π| ++ natWord (prefixValue π))`, `T` gains the count field
`1^{|π|} 0 π`, the input head moves past `frame π`. -/
theorem prefixHead_exec (hIH : IN ≠ HS) (hIT : IN ≠ T) (hHT : HS ≠ T) (σ : WState ns lnr) (π pre rest : List Bool)
    (hst : σ.st IN = pre ++ marks (frame π) ++ rest) (hsh : σ.sh IN = pre.length)
    (hTh : σ.sh T = (σ.st T).length) (hHh : σ.sh HS = (σ.st HS).length)
    (hY : ∀ i, σ.val (cY i) = 0) (hR : ∀ i, σ.val (cR i) = 0)
    (hcap : σ.val rH + 12 * π.length + 30 ≤ cap) :
    WExec cap (prefixHead IN HS T) σ
      (((appendO (appendO σ T (cY 1) (countField π.length (Algorithm.CellCall.prefixValue π))) HS rH
        (marks (natWord π.length ++ natWord (Algorithm.CellCall.prefixValue π)))).seth IN
          (pre.length + (marks (frame π)).length)).setv (cY 1) 0)
      (prefixCost π.length) := by
  have hne12 : cY 1 ≠ cY 2 := by pdst
  have hn1H : cY 1 ≠ rH := by pdst
  have hn2H : cY 2 ≠ rH := by pdst
  have hL := natBitLength_le_self_succ π.length
  have hlenL := NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_length π.length
  -- the ones
  have e1 := frameScan_exec cap IN (onesP T (cY 1) (cY 2)) π pre σ
    ((appendO σ T (cY 1) (List.replicate π.length true)).setv (cY 2) (σ.val (cY 2) + 4 * π.length)) _ hsh
    (onesLoop_frame cap IN T hIT (cY 1) (cY 2) hne12 π pre rest σ hst hTh (by rw [hY]; omega) (by rw [hY]; omega))
  set σ1 := ((appendO σ T (cY 1) (List.replicate π.length true)).setv (cY 2) (σ.val (cY 2) + 4 * π.length)).seth IN
    (pre.length + (marks (frame π)).length) with hσ1
  have h1Y1 : σ1.val (cY 1) = π.length := by simp [hσ1, Function.update_of_ne hne12, hY]
  have h1R : ∀ i : Fin 8, i.val ≠ 0 → i.val ≠ 7 → σ1.val (piRegs i) = 0 := by
    intro i h0 h7
    rw [piRegs, natRegs_mid _ _ _ _ _ i h0 h7]
    simp [hσ1, Function.update_of_ne (show cR ⟨i.val - 1, by omega⟩ ≠ cY 2 by pdst),
      Function.update_of_ne (show cR ⟨i.val - 1, by omega⟩ ≠ cY 1 by pdst), hR]
  have h1H : σ1.val rH = σ.val rH := by
    simp [hσ1, Function.update_of_ne hn2H.symm, Function.update_of_ne hn1H.symm]
  -- `natWord |π|`
  have e2 := writeNatM_spec cap HS piRegs σ1 (h1R 1 (by decide) (by decide)) (h1R 2 (by decide) (by decide))
    (h1R 3 (by decide) (by decide)) (h1R 4 (by decide) (by decide)) (h1R 5 (by decide) (by decide))
    (h1R 6 (by decide) (by decide))
    (by simp [hσ1, Function.update_of_ne hIH.symm, Function.update_of_ne hHT, hHh])
    (by rw [show piRegs 0 = cY 1 from rfl, show piRegs 7 = rH from rfl, h1Y1, h1H]; omega)
  rw [show piRegs 0 = cY 1 from rfl, show piRegs 7 = rH from rfl, h1Y1] at e2
  set σ2 := appendO σ1 HS rH (marks (natWord π.length)) with hσ2
  -- back to the start of `frame π`
  have hfl := marks_frame_length π
  have e3 := NearCubicGates.Close.Codec.rewindLoop_spec cap IN (cY 2) (4 * π.length) σ2
    (by simp [hσ2, hσ1, Function.update_of_ne hn2H, hY]) (by simp [hσ2, hσ1, Function.update_of_ne hIH]; omega)
    (by omega)
  have h2sh : σ2.sh IN - 4 * π.length = pre.length + 1 + 1 := by
    simp [hσ2, hσ1, Function.update_of_ne hIH]; omega
  rw [h2sh] at e3
  have e4 := bwd_at cap IN (σ2.setv (cY 2) 0) (pre.length + 1 + 1)
  have e5 := bwd_at cap IN (σ2.setv (cY 2) 0) (pre.length + 1 + 1 - 1)
  rw [Nat.add_sub_cancel] at e4
  rw [Nat.add_sub_cancel, Nat.add_sub_cancel] at e5
  set σ5 := (σ2.setv (cY 2) 0).seth IN pre.length with hσ5
  -- the zero and the bits
  have h5T : σ5.sh T = (σ5.st T).length := by
    simp [hσ5, hσ2, hσ1, Function.update_of_ne hIT.symm, Function.update_of_ne hHT.symm, hTh]
  have e6 := emitC_app cap T (cY 1) false σ5 h5T
    (by simp [hσ5, hσ2, hσ1, Function.update_of_ne hne12, Function.update_of_ne hn1H, hY]; omega)
  set σ6 := appendO σ5 T (cY 1) [false] with hσ6
  have e7 := frameScan_exec cap IN (bitP IN T (cY 1)) π pre σ6 (appendO σ6 T (cY 1) π) _
    (by simp [hσ6, hσ5, Function.update_of_ne hIT])
    (bitsLoop_frame cap IN T hIT (cY 1) π pre rest σ6
      (by simp [hσ6, hσ5, hσ2, hσ1, Function.update_of_ne hIT, Function.update_of_ne hIH, hst])
      (by simp [hσ6, h5T])
      (by simp [hσ6, hσ5, hσ2, hσ1, Function.update_of_ne hne12, Function.update_of_ne hn1H, hY]; omega))
  set σ7 := (appendO σ6 T (cY 1) π).seth IN (pre.length + (marks (frame π)).length) with hσ7
  -- back to the start of the count field
  have h7Y : σ7.val (cY 1) = π.length + 1 + π.length := by
    simp [hσ7, hσ6, hσ5, hσ2, hσ1, Function.update_of_ne hne12, Function.update_of_ne hn1H, hY]
  have h7T : σ7.st T = σ.st T ++ (List.replicate π.length true ++ false :: π) := by
    simp [hσ7, hσ6, hσ5, hσ2, hσ1, Function.update_of_ne hHT.symm, Function.update_of_ne hIT.symm]
  have h7Th : σ7.sh T = (σ.st T).length + (π.length + 1 + π.length) := by
    simp [hσ7, hσ6, hσ5, hσ2, hσ1, Function.update_of_ne hHT.symm, Function.update_of_ne hIT.symm, hTh]; omega
  have e8 := NearCubicGates.Close.Codec.rewindLoop_spec cap T (cY 1) (π.length + 1 + π.length) σ7 h7Y
    (by omega) (by omega)
  rw [h7Th, Nat.add_sub_cancel] at e8
  set σ8 := (σ7.setv (cY 1) 0).seth T (σ.st T).length with hσ8
  -- the number of `π`
  have h8T : σ8.st T = σ.st T ++ countField π.length (Algorithm.CellCall.prefixValue π) ++ [] := by
    rw [countField_prefix]; simp [hσ8, h7T]
  have h8Th : σ8.sh T = (σ.st T).length := by simp [hσ8]
  have hfield : NearCubicGates.Close.Codec.fieldLen (σ8.st T) (σ8.sh T) = π.length := by
    rw [h8T, h8Th]; exact fieldLen_countField _ _ _ _
  have hX : ∀ i, σ8.val (cY i) = 0 := by
    intro i
    by_cases h1 : cY i = cY 1
    · rw [h1]; simp [hσ8]
    · by_cases h2 : cY i = cY 2
      · rw [h2]
        simp [hσ8, hσ7, hσ6, hσ5, Function.update_of_ne hne12.symm]
      · simp [hσ8, hσ7, hσ6, hσ5, hσ2, hσ1, Function.update_of_ne h1, Function.update_of_ne h2,
          Function.update_of_ne (show cY i ≠ rH by pdst), hY]
  have h8H : σ8.val rH = σ.val rH + (marks (natWord π.length)).length := by
    simp [hσ8, hσ7, hσ6, hσ5, hσ2, hσ1, Function.update_of_ne hn1H.symm, Function.update_of_ne hn2H.symm]
  have e9 := NearCubicGates.Close.Codec.numW_spec cap T HS cY rH hHT.symm (fun i => by pdst) σ8 hX
    (by simp [hσ8, hσ7, hσ6, hσ5, hσ2, hσ1, Function.update_of_ne hIH.symm, Function.update_of_ne hHT, hHh])
    (by rw [hfield]; omega) (by rw [hfield, h8H, marks_length]; omega)
  rw [hfield] at e9
  have hread : (NearCubicGates.Close.Worker.Format.readNum ((σ8.st T).drop (σ8.sh T))).1 =
      Algorithm.CellCall.prefixValue π := by
    rw [h8T, h8Th, List.append_assoc, List.drop_left]
    rw [readNum_countField _ _ (Greedy.prefixValue_lt π)]
  rw [hread] at e9
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6
    (WExec.seq e7 (WExec.seq e8 e9)))))))) ?_ (by unfold prefixCost; omega)
  have hcf : countField π.length (Algorithm.CellCall.prefixValue π) = List.replicate π.length true ++ false :: π :=
    countField_prefix π
  refine WState.eq ?_ ?_ ?_ ?_
  · funext j
    by_cases jH : j = HS
    · subst jH
      simp [hσ8, hσ7, hσ6, hσ5, hσ2, hσ1, Function.update_of_ne hHT, Function.update_of_ne hIH.symm, marks_length]
      omega
    · by_cases jT : j = T
      · subst jT
        simp [hσ8, Function.update_of_ne hHT.symm, Function.update_of_ne hIT.symm, hcf, hTh]
        omega
      · by_cases jI : j = IN
        · subst jI
          simp [hσ8, hσ7, Function.update_of_ne hIH, Function.update_of_ne hIT]
        · simp [hσ8, hσ7, hσ6, hσ5, hσ2, hσ1, Function.update_of_ne jH, Function.update_of_ne jT,
            Function.update_of_ne jI]
  · funext j
    by_cases jH : j = HS
    · subst jH
      simp [hσ8, hσ7, hσ6, hσ5, hσ2, hσ1, Function.update_of_ne hHT, Function.update_of_ne hIH.symm, marks_append]
    · by_cases jT : j = T
      · subst jT
        simp [hσ8, hσ7, hσ6, hσ5, hσ2, hσ1, Function.update_of_ne hHT.symm, Function.update_of_ne hIT.symm, hcf]
      · simp [hσ8, hσ7, hσ6, hσ5, hσ2, hσ1, Function.update_of_ne jH, Function.update_of_ne jT]
  · funext r
    by_cases r1 : r = cY 1
    · subst r1
      simp [hσ8, Function.update_of_ne hn1H]
    · by_cases r2 : r = cY 2
      · subst r2
        simp [hσ8, hσ7, hσ6, hσ5, Function.update_of_ne hn2H, Function.update_of_ne hne12.symm, hY]
      · by_cases rh : r = rH
        · subst rh
          simp [hσ8, hσ7, hσ6, hσ5, hσ2, hσ1, Function.update_of_ne hn1H.symm, Function.update_of_ne hn2H.symm,
            marks_length]
          omega
        · simp [hσ8, hσ7, hσ6, hσ5, hσ2, hσ1, Function.update_of_ne r1, Function.update_of_ne r2,
            Function.update_of_ne rh]
  · simp [hσ8, hσ7, hσ6, hσ5, hσ2, hσ1]

end PrefixHead

end NearQuarticWires.Control
