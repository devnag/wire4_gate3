import Proof.Quartic.Reconstruct.BatchLoopTables

/-!
# Copying the answer of an exact solver

Paper: Step 3 of `sec:algorithm`, paper/paper.tex: the answer of the exact solver on a system is
`solveWord (S.solve s)`: `natWord 0` when the system has no solution, `natWord 1 ++ listWord ratWord F` for the
solution `F` (`Interfaces.Formats.solveWord`). `solveCopier` copies it from the output tape of the solver to the
accumulator and brings the head of the output tape back (`solveCopier_exec`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearQuarticWires.Reconstruct.Batch

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.RepairOrdinary.Streaming (marks marks_length marks_append)
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat (appendO appendO_st appendO_sh appendO_val appendO_cell)
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (enc stp)
open NearQuarticWires.Control
open NearCubicGates.Close.Interfaces (listWord ratWord)
open NearCubicGates.Close.Codec (Rne)

variable {ns nr : ℕ} (cap : ℕ)

/-- Copy `ratWord x`: the numerator, then the denominator. -/
def copyRat (ε : Bool) (s o : Fin (ns + 1)) (R : Fin 8 ↪ Fin nr) : WM ns nr :=
  .seq (NearCubicGates.Close.Codec.copyInt ε s o R) (NearCubicGates.Close.Codec.copyNat ε s o R)

theorem copyRat_spec (ε : Bool) (s o : Fin (ns + 1)) (hso : s ≠ o) (R : Fin 8 ↪ Fin nr) (x : ℚ)
    (pre rest : List Bool) (σ : WState ns nr) (hst : σ.st s = pre ++ enc ε (ratWord x) ++ rest)
    (hsh : σ.sh s = pre.length) (ho : σ.sh o = (σ.st o).length) (h1 : σ.val (R 1) = 0) (h2 : σ.val (R 2) = 0)
    (hcap : σ.val (R 7) + 2 * (ratWord x).length + 4 ≤ cap) :
    WExec cap (copyRat ε s o R) σ
      ((appendO σ o (R 7) (marks (ratWord x))).seth s (pre.length + stp ε * (ratWord x).length))
      (60 * (ratWord x).length + 182) := by
  have hsplit : enc ε (ratWord x) = enc ε (NearCubicGates.Close.Interfaces.intWord x.num) ++
      enc ε (RepairRepresentation.natWord x.den) := by
    unfold ratWord; exact NearCubicWires.WireExponent3_5.PrimAsm.CopyNat.enc_append ε _ _
  have hl : (ratWord x).length = (NearCubicGates.Close.Interfaces.intWord x.num).length +
      (RepairRepresentation.natWord x.den).length := by simp [ratWord]
  have hA := NearCubicGates.Close.Codec.copyInt_spec cap ε s o hso R x.num pre
    (enc ε (RepairRepresentation.natWord x.den) ++ rest) σ
    (by rw [hst, hsplit]; simp [List.append_assoc]) hsh ho h1 h2 (by omega)
  set σ1 := (appendO σ o (R 7) (marks (NearCubicGates.Close.Interfaces.intWord x.num))).seth s
    (pre.length + stp ε * (NearCubicGates.Close.Interfaces.intWord x.num).length) with hσ1
  have hB := NearCubicGates.Close.Codec.copyNat_spec cap ε s o hso R x.den
    (pre ++ enc ε (NearCubicGates.Close.Interfaces.intWord x.num)) rest σ1
    (by simp only [hσ1, WState.seth_st, appendO_st]; rw [Function.update_of_ne hso, hst, hsplit]; simp [List.append_assoc])
    (by simp [hσ1, NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.enc_length])
    (by simp [hσ1, appendO, Function.update_of_ne (Ne.symm hso), ho])
    (by simp [hσ1, appendO, Function.update_of_ne (Rne R (show (1 : Fin 8) ≠ 7 by decide)), h1])
    (by simp [hσ1, appendO, Function.update_of_ne (Rne R (show (2 : Fin 8) ≠ 7 by decide)), h2])
    (by simp only [hσ1, WState.seth_val, appendO_val, Function.update_self]; rw [marks_length]; omega)
  refine WExec.cast cap (WExec.seq hA hB) ?_ (by omega)
  refine WState.eq ?_ ?_ ?_ rfl
  · funext j; by_cases hj : j = s
    · subst hj; simp [hσ1, appendO, Function.update_of_ne hso, ratWord,
        NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.enc_length]; ring
    · by_cases hjo : j = o
      · subst hjo; simp [hσ1, appendO, Function.update_of_ne hj, ho, ratWord, NearCubicGates.Close.Codec.marksApp]; ring
      · simp [hσ1, appendO, Function.update_of_ne hj, Function.update_of_ne hjo]
  · funext j; by_cases hjo : j = o
    · subst hjo; simp [hσ1, appendO, Function.update_of_ne (Ne.symm hso), ratWord, NearCubicGates.Close.Codec.marksApp]
    · by_cases hj : j = s
      · subst hj; simp [hσ1, appendO, Function.update_of_ne hjo]
      · simp [hσ1, appendO, Function.update_of_ne hjo, Function.update_of_ne hj]
  · funext r; by_cases hr7 : r = R 7
    · subst hr7; simp [hσ1, appendO, ratWord, NearCubicGates.Close.Codec.marksApp]; ring
    · simp [hσ1, appendO, Function.update_of_ne hr7]


/-- **The copier of an answer of the solver.** -/
def solveCopier (p : Program) : WM (cns p.tapeCount) lnr :=
  .seq (.fwd (cbank _ p.outputTape)) (.seq (.fwd (cbank _ p.outputTape)) (.ifs (cbank _ p.outputTape)
    (.seq (.bwd (cbank _ p.outputTape)) (.seq (.bwd (cbank _ p.outputTape))
      (.seq (NearCubicGates.Close.Codec.copyNat false (cbank _ p.outputTape) (cT _) cR)
      (.seq (NearCubicGates.Close.Codec.copyList false (cbank _ p.outputTape) (cT _) cR
        (copyRat false (cbank _ p.outputTape) (cT _) cR))
      (halfRewind (cbank _ p.outputTape) (cR 7))))))
    (.seq (.bwd (cbank _ p.outputTape)) (.seq (.bwd (cbank _ p.outputTape))
      (.seq (NearCubicGates.Close.Codec.copyNat false (cbank _ p.outputTape) (cT _) cR)
        (halfRewind (cbank _ p.outputTape) (cR 7)))))))

/-- The cost of copying an answer. -/
def solveCopyCost : Option (List ℚ) → ℕ
  | none => 300
  | some F => 1 + 1 + (1 + 1 + (1 + 1 + (1 + 1 + 1 + (60 * 3 + 60 + 1 +
      (NearCubicGates.Close.Codec.copyListCost F.length (F.map fun x => 60 * (ratWord x).length + 182) + 1 +
        ((NearCubicGates.Close.Interfaces.Formats.solveWord (some F)).length * 7 + 1))))))

theorem natWord_zero_eq : RepairRepresentation.natWord 0 = [true, false, false] := by decide
theorem natWord_one_eq : RepairRepresentation.natWord 1 = [true, false, true] := by decide

theorem solveCopier_exec (p : Program) (a : Option (List ℚ)) (σ : WState (cns p.tapeCount) lnr)
    (hO : σ.st (cbank _ p.outputTape) = NearCubicGates.Close.Interfaces.Formats.solveWord a)
    (hOh : σ.sh (cbank _ p.outputTape) = 0) (hT : σ.sh (cT _) = (σ.st (cT _)).length) (hR : ∀ i, σ.val (cR i) = 0)
    (hcap : 2 ^ ((NearCubicGates.Close.Interfaces.Formats.solveWord a).length + 2) +
      10 * (NearCubicGates.Close.Interfaces.Formats.solveWord a).length + 20 ≤ cap) :
    WExec cap (solveCopier p) σ (appendT σ (cT _) (marks (NearCubicGates.Close.Interfaces.Formats.solveWord a)))
      (solveCopyCost a) := by
  have hOT : cbank p.tapeCount p.outputTape ≠ cT _ := cne _ (by simp [cbank, cT]; omega)
  have e1 : WExec cap (.fwd (cbank _ p.outputTape)) σ (σ.seth (cbank _ p.outputTape) (0 + 1)) 1 := by
    have := WExec.fwd (cap := cap) (cbank _ p.outputTape) σ
    rwa [hOh] at this
  have e2 := fwd_at cap (cbank _ p.outputTape) σ (0 + 1)
  have b1 := bwd_at cap (cbank _ p.outputTape) σ (0 + 1 + 1)
  have b2 := bwd_at cap (cbank _ p.outputTape) σ (0 + 1 + 1 - 1)
  rw [show 0 + 1 + 1 - 1 - 1 = σ.sh (cbank _ p.outputTape) by omega, seth_self] at b2
  have hlen := congrArg List.length hO
  cases a with
  | none =>
    simp only [NearCubicGates.Close.Interfaces.Formats.solveWord] at hO hcap hlen ⊢
    rw [natWord_zero_eq] at hO hcap hlen ⊢
    norm_num at hcap
    have hb : wbit (σ.seth (cbank _ p.outputTape) (0 + 1 + 1)) (cbank _ p.outputTape) = false := by
      simp [wbit, hO, readTapeBit]
    have c1 := NearCubicGates.Close.Codec.copyNat_spec cap false (cbank _ p.outputTape) (cT _) hOT cR 0 [] [] σ
      (by rw [hO, natWord_zero_eq]; rfl) hOh hT (hR 1) (hR 2) (by rw [hR 7, natWord_zero_eq]; simp; omega)
    rw [natWord_zero_eq] at c1
    have c2 := halfRewind_spec cap (cbank _ p.outputTape) (cR 7) 3
      ((appendO σ (cT _) (cR 7) (marks [true, false, false])).seth (cbank _ p.outputTape)
        (([] : List Bool).length + stp false * [true, false, false].length))
      (by simp [hR 7, marks]) (by omega)
    refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.ifsF hb (WExec.seq b1 (WExec.seq b2
      (WExec.seq c1 c2)))))) ?_ (by simp [solveCopyCost])
    refine WState.eq ?_ ?_ ?_ rfl
    · funext q
      by_cases hq : q = cbank p.tapeCount p.outputTape
      · subst hq; simp [appendT, Function.update_of_ne hOT, hOh, stp]
      · by_cases hT' : q = cT _
        · subst hT'; simp [appendT, Function.update_of_ne hOT.symm]
        · simp [appendT, Function.update_of_ne hq, Function.update_of_ne hT']
    · funext q; by_cases hT' : q = cT _
      · subst hT'; simp [appendT]
      · simp [appendT, Function.update_of_ne hT']
    · funext r; by_cases hr : r = cR 7
      · subst hr; simp [appendT, hR 7]
      · simp [appendT, Function.update_of_ne hr]
  | some F =>
    simp only [NearCubicGates.Close.Interfaces.Formats.solveWord] at hO hcap hlen ⊢
    rw [natWord_one_eq] at hO hcap hlen ⊢
    have hlw := (listWord_count ratWord F (fun x => by
      have := natBitLength_le_intWord x.num; simp [ratWord]; omega))
    obtain ⟨hlw1, hlw2⟩ := hlw
    have hL : ([true, false, true] ++ listWord ratWord F).length = 3 + (listWord ratWord F).length := by
      simp; omega
    have hpw : 2 ^ (natBitLength F.length + 1) ≤ 2 ^ (([true, false, true] ++ listWord ratWord F).length + 2) :=
      Nat.pow_le_pow_right (by norm_num) (by rw [hL]; omega)
    have hp0 : ([true, false, true] ++ listWord ratWord F).length < 2 ^ (([true, false, true] ++ listWord ratWord F).length + 2) :=
      lt_trans Nat.lt_two_pow_self (Nat.pow_lt_pow_right (by norm_num) (by omega))
    have hb : wbit (σ.seth (cbank _ p.outputTape) (0 + 1 + 1)) (cbank _ p.outputTape) = true := by
      simp [wbit, hO, readTapeBit]
    have c1 := NearCubicGates.Close.Codec.copyNat_spec cap false (cbank _ p.outputTape) (cT _) hOT cR 1 []
      (listWord ratWord F) σ (by rw [hO, natWord_one_eq]; rfl) hOh hT (hR 1) (hR 2)
      (by rw [hR 7, natWord_one_eq]; simp; omega)
    rw [natWord_one_eq] at c1
    set σ1 := (appendO σ (cT _) (cR 7) (marks [true, false, true])).seth (cbank _ p.outputTape)
      (([] : List Bool).length + stp false * [true, false, true].length) with hσ1
    have c2 := NearCubicGates.Close.Codec.copyList_spec cap false (cbank _ p.outputTape) (cT _) hOT cR
      (copyRat false (cbank _ p.outputTape) (cT _) cR) ratWord (fun x => 60 * (ratWord x).length + 182)
      (fun τ => τ.val (cR 1) = 0 ∧ τ.val (cR 2) = 0) (2 * ([true, false, true] ++ listWord ratWord F).length)
      (fun τ x h => h)
      (fun τ x h => ⟨by simp [Function.update_of_ne (Rne cR (show (1 : Fin 8) ≠ 0 by decide)), h.1],
        by simp [Function.update_of_ne (Rne cR (show (2 : Fin 8) ≠ 0 by decide)), h.2]⟩)
      (fun τ w h => ⟨by simp [Function.update_of_ne (Rne cR (show (1 : Fin 8) ≠ 7 by decide)), h.1],
        by simp [Function.update_of_ne (Rne cR (show (2 : Fin 8) ≠ 7 by decide)), h.2]⟩) F
      (fun x hx pre rest τ hτ hst hsh ho hV => copyRat_spec cap false _ _ hOT cR x pre rest τ hst hsh ho hτ.1 hτ.2
        (by rw [marks_length] at hV; omega))
      [true, false, true] [] σ1
      ⟨by simp [hσ1, Function.update_of_ne (Rne cR (show (1 : Fin 8) ≠ 7 by decide)), hR 1],
        by simp [hσ1, Function.update_of_ne (Rne cR (show (2 : Fin 8) ≠ 7 by decide)), hR 2]⟩
      (by simp [hσ1, Function.update_of_ne hOT, hO, NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.enc])
      (by simp [hσ1, stp])
      (by simp [hσ1, Function.update_of_ne hOT.symm, hT])
      (fun i hi => by simp [hσ1, Function.update_of_ne (Rne cR hi), hR i])
      (by omega) (by omega)
      (by simp [hσ1, hR 7, marks]; have := natBitLength_le_self_succ F.length; omega)
      (by simp [hσ1, hR 7, marks_length]; omega)
    set σ2 := (appendO σ1 (cT _) (cR 7) (marks (listWord ratWord F))).seth (cbank _ p.outputTape)
      ([true, false, true].length + stp false * (listWord ratWord F).length) with hσ2
    have c3 := halfRewind_spec cap (cbank _ p.outputTape) (cR 7) ([true, false, true] ++ listWord ratWord F).length σ2
      (by simp [hσ2, hσ1, hR 7, marks_length]; omega) (by omega)
    refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.ifsT hb (WExec.seq b1 (WExec.seq b2
      (WExec.seq c1 (WExec.seq c2 c3))))))) ?_ (by
        simp only [solveCopyCost, NearCubicGates.Close.Interfaces.Formats.solveWord, natWord_one_eq, List.length_append,
          List.length_cons, List.length_nil]
        omega)
    refine WState.eq ?_ ?_ ?_ rfl
    · funext q
      by_cases hq : q = cbank p.tapeCount p.outputTape
      · subst hq; simp [hσ2, hσ1, appendT, Function.update_of_ne hOT, hOh, stp]; omega
      · by_cases hT' : q = cT _
        · subst hT'; simp [hσ2, hσ1, appendT, Function.update_of_ne hOT.symm, marks_length]; ring
        · simp [hσ2, hσ1, appendT, Function.update_of_ne hq, Function.update_of_ne hT']
    · funext q; by_cases hT' : q = cT _
      · subst hT'; simp [hσ2, hσ1, appendT, ← marks_append]
      · simp [hσ2, hσ1, appendT, Function.update_of_ne hT']
    · funext r; by_cases hr : r = cR 7
      · subst hr; simp [hσ2, hσ1, appendT, hR 7]
      · simp [hσ2, hσ1, appendT, Function.update_of_ne hr]


theorem solveCopier_avoids (p : Program) : WM.Avoids (cOUT p.tapeCount) (solveCopier p) := by
  simp [WM.Avoids, solveCopier, copyRat, halfRewind, NearCubicGates.Close.Codec.copyList,
    NearCubicGates.Close.Codec.listLoop, NearCubicGates.Close.Codec.copyInt, NearCubicGates.Close.Codec.copyNat,
    NearCubicWires.WireExponent3_5.PrimAsm.CopyNat.copyNatM, NearCubicWires.WireExponent3_5.PrimAsm.CopyNat.copyUnary,
    NearCubicWires.WireExponent3_5.PrimAsm.CopyNat.copyBit, NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.preE,
    NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.readNatM, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.writeNatM,
    NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.emitPair, emitC, WM.fwdC, cbank, cT, cOUT, Fin.ext_iff,
    NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.unaryBody, NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.bitBody,
    NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.addTo, NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.dbl,
    NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.dblLoop, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.bitLenM,
    NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.prefixM, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.payM,
    NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.payBody, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.halveM,
    NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.halveLoop, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.lenLoop,
    NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.onesLoop, NearCubicWires.WireExponent3_5.FinalPass.Hash4.wcopyR,
    NearCubicWires.WireExponent3_5.FinalPass.Hash4.wdup, WM.clear, WM.move]
  all_goals omega

theorem sum_ratWord_le (F : List ℚ) :
    (F.map fun x => 60 * (ratWord x).length + 182 + 4).sum ≤
      60 * (F.flatMap ratWord).length + 186 * F.length := by
  induction F with
  | nil => simp
  | cons x F ih => simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.length_append,
      List.length_cons]; omega

/-- **The cost of copying an answer** is linear in the answer, with the bit length of its count. -/
theorem solveCopyCost_le (a : Option (List ℚ)) (L m : ℕ)
    (hL : ∀ F, a = some F → natBitLength F.length ≤ L ∧ F.length ≤ m) :
    solveCopyCost a ≤ 300 * (L + 10) * (m + 2) +
      70 * (NearCubicGates.Close.Interfaces.Formats.solveWord a).length + 300 := by
  cases a with
  | none => simp [solveCopyCost]
  | some F =>
    obtain ⟨hL1, hm⟩ := hL F rfl
    have hp := two_pow_natBitLength_le F.length
    have hsum := sum_ratWord_le F
    have hlw : (F.flatMap ratWord).length ≤ (listWord ratWord F).length := by simp [listWord]
    have h1 : (natBitLength F.length + 2) * (40 * 2 ^ natBitLength F.length + 40) ≤ (L + 10) * (80 * m + 120) :=
      Nat.mul_le_mul (by omega) (by omega)
    have h2 : (natBitLength F.length + 10) * (100 * F.length + 200) ≤ (L + 10) * (100 * m + 200) :=
      Nat.mul_le_mul (by omega) (by omega)
    have hsw : (NearCubicGates.Close.Interfaces.Formats.solveWord (some F)).length =
        3 + (listWord ratWord F).length := by
      simp [NearCubicGates.Close.Interfaces.Formats.solveWord, natWord_one_eq]; omega
    simp only [solveCopyCost, NearCubicGates.Close.Codec.copyListCost]
    rw [hsw]
    rw [List.map_map] at *
    simp only [Function.comp_def] at *
    nlinarith

end NearQuarticWires.Reconstruct.Batch
