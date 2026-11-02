import Proof.Quartic.StageRecovery.FamilyHeader

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery
open NearCubicWires
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells NearCubicGates.Close.Expand
open NearCubicGates.Close.Interfaces.Formats

/-- `lem:print`, paper/paper.tex: actual source parsing
leaves its head exactly at the original Formula tokens and retains all
previous physical stores and buffers. -/
theorem familyHeaderProgram_suffix_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (r : FamilyCompileRequest) (suffix : List Bool) (hin : C.inp.drop a.ip = r.word ++ suffix)
    (hwidth : ∀ v ∈ r.header, natBitLength v + 2 ≤ C.Wd) :
    Hs C familyHeaderProgram a (StageGamma.readFieldsCost r.header) (fun b =>
      b.env familyBoundVar = r.degree ∧ b.env arityVar = r.source.arity ∧
      b.env familyHintVar = r.setupHint ∧ b.env widthVar = r.source.hint ∧
      b.env modulusVar = r.source.modulus ∧ b.env tokenCountVar = (toks r.source.formula).length ∧
      b.env tokenLengthVar = (tokenStream (toks r.source.formula)).length ∧
      b.ip = a.ip + (r.header.flatMap natWord).length ∧
      (b.out, b.ram, b.rc, b.kin, b.kout, b.kc) = (a.out, a.ram, a.rc, a.kin, a.kout, a.kc) ∧
      Cst b ∧ Fr a b (familyHeaderVars ++ vJ :: rdNatT)) := by
  refine (StageGamma.readFields_spec C familyHeaderVars (by decide) (by decide)
    r.header (by simp [familyHeaderVars, FamilyCompileRequest.header]) a hc
    (tokenStream (toks r.source.formula) ++ suffix)
      (by rw [r.word_eq_header, List.append_assoc] at hin; exact hin) hwidth).mono le_rfl ?_
  rintro b ⟨hv, hi, hr, hbc, hf⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hi, hr, hbc, hf⟩
  · simpa [familyHeaderVars, FamilyCompileRequest.header] using hv ⟨1, by decide⟩
  · simpa [familyHeaderVars, FamilyCompileRequest.header] using hv ⟨5, by decide⟩
  · simpa [familyHeaderVars, FamilyCompileRequest.header] using hv ⟨0, by decide⟩
  · simpa [familyHeaderVars, FamilyCompileRequest.header] using hv ⟨3, by decide⟩
  · simpa [familyHeaderVars, FamilyCompileRequest.header] using hv ⟨4, by decide⟩
  · simpa [familyHeaderVars, FamilyCompileRequest.header] using hv ⟨6, by decide⟩
  · simpa [familyHeaderVars, FamilyCompileRequest.header] using hv ⟨2, by decide⟩


end NearQuarticWires.StageRecovery
