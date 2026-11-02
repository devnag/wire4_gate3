import Proof.Quartic.StageRecovery.ModReduce
import Proof.Quartic.StageRecovery.PacketFields

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicWires NearCubicGates.Close.Cells NearCubicGates.Close.Expand

/-- `lem:print`, paper/paper.tex: the decoded signed
constant is reduced before it is pushed onto the binary formula stack. -/
def constantModCore : St VV MM :=
  .seq reduceLeftProgram
    (.seq (.ite (.eq signVar v1) (negateModProgram leftVar) skipS) pushModStack)

/-- `lem:print`, paper/paper.tex: the physical signed
constant operation gives a reduced residue and preserves the complete
remaining stack and all retained formula metadata. -/
theorem constantModCore_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (q magnitude : ℕ) (negative : Bool) (xs : List ℕ) (hq : 2 ≤ q)
    (haq : a.env modulusVar = q) (ham : a.env leftVar = magnitude)
    (has : a.env signVar = negative.toNat) (hstack : a.env stackVar = senc q xs)
    (hxs : ∀ x ∈ xs, x < q) (hdepth : q ^ (xs.length + 2) ≤ 2 ^ C.Wd) :
    Hs C constantModCore a 18 (fun b =>
      b.env stackVar = senc q (signedNaturalResidue q magnitude negative :: xs) ∧
      b.env modulusVar = q ∧ b.sh = a.sh ∧ Cst b ∧
      Fr a b [stackVar, leftVar, productVar, quotientVar, remainderVar, vJ]) := by
  obtain ⟨_, h2q, _, hnew⟩ := depth_facts xs hq hdepth
  have hres : signedNaturalResidue q magnitude negative < q := by
    cases negative <;> exact Nat.mod_lt _ (by omega)
  have hpush : senc q (signedNaturalResidue q magnitude negative :: xs) < 2 ^ C.Wd :=
    hnew _ (by simp) (by
      intro value hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact hres
      · exact hxs value hv)
  unfold constantModCore
  refine Hs.seq (t2 := 14) (reduceLeftProgram_spec C a (by rw [haq]; omega)
    (by rw [haq]; exact h2q)) fun b ⟨hbl, hbsh, hbf⟩ => ?_
  have hbq : b.env modulusVar = q := by rw [hbf _ (by decide), haq]
  have hbs : b.env signVar = negative.toNat := by rw [hbf _ (by decide), has]
  have hbc : Cst b := Cst.of_fr hc hbf (by decide)
  have hbl' : b.env leftVar = magnitude % q := by simpa only [ham, haq] using hbl
  have ec : Hs C (.ite (.eq signVar v1) (negateModProgram leftVar) skipS) b 8
      (fun d => d.env leftVar = signedNaturalResidue q magnitude negative ∧ d.sh = b.sh ∧
        Cst d ∧ Fr b d [leftVar, productVar, quotientVar, remainderVar, vJ]) := by
    cases negative with
    | false =>
        have he : (Cnd.eq signVar v1).eval b = false := by simp [Cnd.eval, hbs, hbc.one]
        refine ((Hs.iteF (c := .eq signVar v1) (show signVar ≠ v1 by decide) he
          (skip_spec b))).mono (by omega) ?_
        rintro d rfl
        exact ⟨by simpa (config := {decide := true}) [DS.set, signedNaturalResidue] using hbl',
          rfl, Cst.of_fr (T := [vJ]) hbc (Fr.set _ _ (by decide)) (by decide), Fr.set _ _ (by decide)⟩
    | true =>
        have he : (Cnd.eq signVar v1).eval b = true := by simp [Cnd.eval, hbs, hbc.one]
        refine (Hs.iteT (c := .eq signVar v1) (show signVar ≠ v1 by decide) he
          (negateModProgram_spec C b leftVar (by decide)
            (by rw [hbq]; omega) (by rw [hbq]; exact h2q)
            (by rw [hbl', hbq]; exact (Nat.mod_lt _ (by omega)).le))).mono le_rfl ?_
        rintro d ⟨hdl, hdsh, hdf⟩
        exact ⟨by simpa only [signedNaturalResidue, if_true, hbl', hbq] using hdl,
          hdsh, Cst.of_fr hbc hdf (by decide), Fr.weaken hdf (by decide)⟩
  refine Hs.seq (t2 := 5) ec fun d ⟨hdl, hdsh, hdc, hdf⟩ => ?_
  have hdq : d.env modulusVar = q := by rw [hdf _ (by decide), hbq]
  have hds : d.env stackVar = senc q xs := by rw [hdf _ (by decide), hbf _ (by decide), hstack]
  refine (pushModStack_spec C d q _ xs hdq hdl hds hpush).mono le_rfl ?_
  rintro e ⟨hes, hesh, hef⟩
  exact ⟨hes, by rw [hef _ (by decide), hdq], hesh.trans (hdsh.trans hbsh),
    Cst.of_fr hdc hef (by decide), Fr.trans (Fr.weaken hbf (by decide))
      (Fr.trans (Fr.weaken hdf (by decide)) (Fr.weaken hef (by decide)))⟩

/-- `lem:print`, paper/paper.tex: the literal integer
payload is parsed from its two original natural fields. -/
def constantModHandler : St VV MM :=
  .seq (readVariable signVar) (.seq (readVariable leftVar) constantModCore)

/-- `lem:print`, paper/paper.tex: an actual signed
constant payload is consumed byte for byte, reduced, and pushed onto
the postfix stack without an unreduced-value output field. -/
theorem constantModHandler_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (q : ℕ) (value : ℤ) (xs : List ℕ) (rest : List Bool) (hq : 2 ≤ q)
    (haq : a.env modulusVar = q) (hstack : a.env stackVar = senc q xs)
    (hxs : ∀ x ∈ xs, x < q) (hdepth : q ^ (xs.length + 2) ≤ 2 ^ C.Wd)
    (hin : C.inp.drop a.ip = NearCubicGates.Close.Interfaces.intWord value ++ rest)
    (hwidth : natBitLength value.natAbs + 2 ≤ C.Wd) (hW : 3 ≤ C.Wd) :
    Hs C constantModHandler a (30 * natBitLength value.natAbs + 114) (fun b =>
      b.env stackVar = senc q ((value % (q : ℤ)).toNat :: xs) ∧
      b.env modulusVar = q ∧ b.ip = a.ip + (NearCubicGates.Close.Interfaces.intWord value).length ∧
      (b.out, b.ram, b.rc, b.kin, b.kout, b.kc) =
        (a.out, a.ram, a.rc, a.kin, a.kout, a.kc) ∧ Cst b ∧ Fr a b evalScratch) := by
  let negative := decide (value < 0)
  let sign := negative.toNat
  have hbits : natBitLength sign = 1 := by
    dsimp [sign, negative]
    by_cases h : value < 0 <;> simp [h, NearCubicWires.natBitLength]
  have hword : NearCubicGates.Close.Interfaces.intWord value =
      NearCubicWires.RepairRepresentation.natWord sign ++
        NearCubicWires.RepairRepresentation.natWord value.natAbs := by
    by_cases h : value < 0 <;> simp [NearCubicGates.Close.Interfaces.intWord, sign, negative, h]
  unfold constantModHandler
  have er := readVariable_spec C a hc signVar (by decide) (by decide) sign _
    (by simpa only [hword, List.append_assoc] using hin) (by rw [hbits]; omega)
  rw [hbits] at er
  refine (Hs.seq (t2 := 30 * natBitLength value.natAbs + 51) er
    fun b ⟨hbs, hbi, hbr, hbc, hbf⟩ => ?_).mono (by omega) (fun _ h => h)
  have hbin : C.inp.drop b.ip = NearCubicWires.RepairRepresentation.natWord value.natAbs ++ rest := by
    rw [hbi, ← List.drop_drop, hin, hword, List.append_assoc, List.drop_left]
  refine (Hs.seq (t2 := 18) (readVariable_spec C b hbc leftVar (by decide) (by decide)
    value.natAbs rest hbin hwidth) fun d ⟨hdl, hdi, hdr, hdc, hdf⟩ => ?_).mono
      (by omega) (fun _ h => h)
  have hdq : d.env modulusVar = q := by rw [hdf _ (by decide), hbf _ (by decide), haq]
  have hds : d.env signVar = negative.toNat := by rw [hdf _ (by decide), hbs]
  have hdst : d.env stackVar = senc q xs := by rw [hdf _ (by decide), hbf _ (by decide), hstack]
  refine (constantModCore_spec C d hdc q value.natAbs negative xs hq hdq hdl hds hdst hxs hdepth).mono le_rfl ?_
  rintro e ⟨hes, heq, hesh, hec, hef⟩
  have hev : signedNaturalResidue q value.natAbs negative = (value % (q : ℤ)).toNat := by
    have h := signedNaturalResidue_eq q (by omega) value
    exact_mod_cast congrArg Int.toNat h
  have hsame := Same.of_sh hesh
  refine ⟨by rw [← hev]; exact hes, heq, ?_, ?_, hec, ?_⟩
  · rw [hsame.ip, hdi, hbi, hword, List.length_append]
    omega
  · have hdout : (d.out, d.ram, d.rc, d.kin, d.kout, d.kc) =
        (a.out, a.ram, a.rc, a.kin, a.kout, a.kc) := hdr.trans hbr
    simpa only [hsame.out, hsame.ram, hsame.rc, hsame.kin, hsame.kout, hsame.kc] using hdout
  · exact Fr.trans (Fr.weaken hbf (by decide))
      (Fr.trans (Fr.weaken hdf (by decide)) (Fr.weaken hef (by decide)))

end NearQuarticWires.StageRecovery
