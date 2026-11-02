import Proof.Quartic.StageRecovery.ModVariable
import Proof.Quartic.StageRecovery.ModConstant

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicWires NearCubicGates.Close.Cells NearCubicGates.Close.Expand
open NearCubicWires.RepairRepresentation (natWord)

/-- `lem:print`, paper/paper.tex: a variable token
parses its original atom index, extracts its bit, and pushes that bit. -/
def variableModHandler : St VV MM :=
  .seq (readVariable atomVar) (.seq variableBitProgram pushModStack)

/-- `lem:print`, paper/paper.tex: the complete variable
payload operation reads only its actual codec and preserves the
original Boolean coordinates and the remaining postfix stack. -/
theorem variableModHandler_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (q point atom : ℕ) (xs : List ℕ) (rest : List Bool) (hq : 2 ≤ q)
    (haq : a.env modulusVar = q) (hap : a.env pointVar = point)
    (hstack : a.env stackVar = senc q xs) (hxs : ∀ x ∈ xs, x < q)
    (hdepth : q ^ (xs.length + 2) ≤ 2 ^ C.Wd)
    (hin : C.inp.drop a.ip = natWord atom ++ rest)
    (hwidth : natBitLength atom + 2 ≤ C.Wd) (hafit : atom < 2 ^ C.Wd) :
    Hs C variableModHandler a (30 * natBitLength atom + atom * 5 + 49) (fun b =>
      b.env stackVar = senc q (pointBit point atom :: xs) ∧
      b.env modulusVar = q ∧ b.ip = a.ip + (natWord atom).length ∧
      (b.out, b.ram, b.rc, b.kin, b.kout, b.kc) =
        (a.out, a.ram, a.rc, a.kin, a.kout, a.kc) ∧ Cst b ∧ Fr a b evalScratch) := by
  obtain ⟨_, h2q, _, hnew⟩ := depth_facts xs hq hdepth
  have h4 : 4 ≤ 2 ^ C.Wd := by omega
  have hres : pointBit point atom < q := by unfold pointBit; split <;> omega
  have hpush : senc q (pointBit point atom :: xs) < 2 ^ C.Wd :=
    hnew _ (by simp) (by
      intro value hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact hres
      · exact hxs value hv)
  unfold variableModHandler
  refine (Hs.seq (t2 := atom * 5 + 16) (readVariable_spec C a hc atomVar
    (by decide) (by decide) atom rest hin hwidth) fun b ⟨hba, hbi, hbr, hbc, hbf⟩ => ?_).mono
      (by omega) (fun _ h => h)
  have hbp : b.env pointVar = point := by rw [hbf _ (by decide), hap]
  refine Hs.seq (t2 := 5) (variableBitProgram_spec C b hbc point atom hbp hba hafit h4)
    fun d ⟨hdl, hdsh, hdc, hdf⟩ => ?_
  have hdq : d.env modulusVar = q := by rw [hdf _ (by decide), hbf _ (by decide), haq]
  have hds : d.env stackVar = senc q xs := by rw [hdf _ (by decide), hbf _ (by decide), hstack]
  refine (pushModStack_spec C d q _ xs hdq hdl hds hpush).mono le_rfl ?_
  rintro e ⟨hes, hesh, hef⟩
  have heSame := Same.of_sh (hesh.trans hdsh)
  refine ⟨hes, by rw [hef _ (by decide), hdq], by rw [heSame.ip, hbi], ?_,
    Cst.of_fr hdc hef (by decide), ?_⟩
  · simpa only [heSame.out, heSame.ram, heSame.rc, heSame.kin, heSame.kout, heSame.kc] using hbr
  · exact Fr.trans (Fr.weaken hbf (by decide))
      (Fr.trans (Fr.weaken hdf (by decide)) (Fr.weaken hef (by decide)))

/-- `lem:print`, paper/paper.tex: the unary exponent
is parsed from its actual codec before repeated reduced multiplication. -/
def powerPayloadHandler : St VV MM := .seq (readVariable exponentVar) (unaryModHandler true)

/-- `lem:print`, paper/paper.tex: the physical power
payload consumes its literal field and never materializes an unreduced
integer power in its source or output. -/
theorem powerPayloadHandler_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (q exponent : ℕ) (xs : List ℕ) (rest : List Bool) (hq : 2 ≤ q)
    (haq : a.env modulusVar = q) (hstack : a.env stackVar = senc q xs)
    (hxs : ∀ x ∈ xs, x < q) (hdepth : q ^ (xs.length + 3) ≤ 2 ^ C.Wd)
    (hin : C.inp.drop a.ip = natWord exponent ++ rest)
    (hwidth : natBitLength exponent + 2 ≤ C.Wd) (hefit : exponent < 2 ^ C.Wd) :
    Hs C powerPayloadHandler a (30 * natBitLength exponent + exponent * 9 + 55) (fun b =>
      b.env stackVar = senc q ((xs.headD 0) ^ exponent % q :: xs.tail) ∧
      b.env modulusVar = q ∧ b.ip = a.ip + (natWord exponent).length ∧
      (b.out, b.ram, b.rc, b.kin, b.kout, b.kc) =
        (a.out, a.ram, a.rc, a.kin, a.kout, a.kc) ∧ Cst b ∧ Fr a b evalScratch) := by
  unfold powerPayloadHandler
  refine (Hs.seq (t2 := exponent * 9 + 22) (readVariable_spec C a hc exponentVar
    (by decide) (by decide) exponent rest hin hwidth) fun b ⟨hbe, hbi, hbr, hbc, hbf⟩ => ?_).mono
      (by omega) (fun _ h => h)
  have hbq : b.env modulusVar = q := by rw [hbf _ (by decide), haq]
  have hbs : b.env stackVar = senc q xs := by rw [hbf _ (by decide), hstack]
  refine (unaryModHandler_spec C b hbc true q exponent xs hq hxs hbq (fun _ => hbe)
    (fun _ => hefit) hbs hdepth).mono le_rfl ?_
  rintro d ⟨hds, hdq, hdsh, hdc, hdf⟩
  have hsame := Same.of_sh hdsh
  exact ⟨hds, hdq, by rw [hsame.ip, hbi],
    by simpa only [hsame.out, hsame.ram, hsame.rc, hsame.kin, hsame.kout, hsame.kc] using hbr,
      hdc, Fr.trans (Fr.weaken hbf (by decide)) (Fr.weaken hdf (by decide))⟩

end NearQuarticWires.StageRecovery
