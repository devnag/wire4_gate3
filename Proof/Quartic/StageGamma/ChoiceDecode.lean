import Proof.Quartic.StageGamma.DigitRegisters

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageGamma

open NearCubicGates.Close.Cells

/-- `cor:conditional`, paper/paper.tex: the current
coefficient's original address is preserved across its eight divisions. -/
def gammaAddress : Fin VV := ⟨95, by decide⟩

/-- `cor:conditional`, paper/paper.tex: the actual
eight-coordinate decoder is a fixed finite ordinary program. -/
def decodeChoice : St VV MM :=
  .seq (.op (.copy gammaWork gammaAddress))
    (readChoiceDigits (List.ofFn gammaDigit))

/-- `cor:conditional`, paper/paper.tex: each true
choice coordinate occupies a different binary destination register. -/
theorem gammaDigit_injective : Function.Injective gammaDigit := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  dsimp [gammaDigit] at this
  omega

/-- `cor:conditional` and `prop:time`, paper/paper.tex: exact sample-choice digits are physically decoded from the
ORIGINAL address in constant source time, including the Q=0/base-one case. -/
theorem decodeChoice_run (C : Ctx) (Q : ℕ) (address : Fin ((Q + 1) ^ 8))
    (a : DS VV MM) (hc : Cst a) (hb : a.env gammaBase = Q + 1)
    (ha : a.env gammaAddress = address.val) (hwidth : 2 * (Q + 1) ≤ 2 ^ C.Wd) :
    Hs C decodeChoice a 35 (fun b =>
      (∀ slot, b.env (gammaDigit slot) = (littleChoiceEquiv Q address slot).val) ∧
      Same a b ∧ Cst b ∧ Fr a b (choiceDigitScratch (List.ofFn gammaDigit))) := by
  unfold decodeChoice
  refine Hs.seq (t1 := 1) (t2 := 33) (hs_copy C gammaWork gammaAddress a (by decide)) ?_
  intro b hbstate
  subst hbstate
  let b := a.set gammaWork (a.env gammaAddress)
  have hf : Fr a b (choiceDigitScratch (List.ofFn gammaDigit)) :=
    Fr.set a _ (by simp [choiceDigitScratch])
  have hbc : Cst b := Cst.of_fr hc (Fr.set a _ (by simp : gammaWork ∈ [gammaWork])) (by decide)
  have hbb : b.env gammaBase = Q + 1 := by rw [DS.set_env_ne _ _ (by decide)]; exact hb
  have hbw : b.env gammaWork = address.val := by simp [b, ha]
  have hsafe : ∀ x ∈ List.ofFn gammaDigit,
      x ∉ [gammaWork, gammaBase, gammaQuotient, vJ, vZ, v1, v2] := by
    intro x hx
    obtain ⟨slot, rfl⟩ := List.mem_ofFn.mp hx
    fin_cases slot <;> decide
  refine Hs.mono (readChoiceDigits_run C (List.ofFn gammaDigit)
    (List.nodup_ofFn.mpr gammaDigit_injective) hsafe b hbc (Q + 1) address.val
    (by omega) hbb hbw hwidth) (by simp) ?_
  intro e ⟨he, _, hes, hec, hef⟩
  refine ⟨?_, (Same.set a _ _).trans hes, hec, hf.trans hef⟩
  intro slot
  have hh := he ⟨slot.val, by simp⟩
  simpa only [Fin.getElem_fin, List.getElem_ofFn, littleChoice_digit] using hh

end NearQuarticWires.StageGamma
