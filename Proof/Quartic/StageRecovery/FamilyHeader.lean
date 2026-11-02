import Proof.Quartic.StageRecovery.FamilySource
import Proof.Quartic.StageRecovery.CacheRecord
import Proof.Quartic.StageGamma.ReadFields

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicWires
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells NearCubicGates.Close.Expand
open NearCubicGates.Close.Interfaces.Formats

/-- `lem:print`, paper/paper.tex: the explicit degree
upper bound is read from its actual serialized metadata field. -/
def familyBoundVar : Fin VV := ⟨114, by decide⟩
/-- `lem:print`, paper/paper.tex: the finite support
mask is computed from the original Formula arity. -/
def familyMaskVar : Fin VV := ⟨115, by decide⟩
/-- `prop:time`, paper/paper.tex: the actual leading
structural setup hint is retained separately from the inner Formula hint. -/
def familyHintVar : Fin VV := ⟨116, by decide⟩

/-- `lem:print`, paper/paper.tex: seven literal natural
fields precede the unchanged original Formula token stream. -/
def familyHeaderVars : List (Fin VV) :=
  [familyHintVar, familyBoundVar, tokenLengthVar, widthVar, modulusVar, arityVar, tokenCountVar]

/-- `lem:print`, paper/paper.tex: the exact finite
compiler header includes the original arity, token count and both paid
metadata fields; it includes no support list or polynomial values. -/
def FamilyCompileRequest.header (r : FamilyCompileRequest) : List ℕ :=
  [r.setupHint, r.degree, (tokenStream (toks r.source.formula)).length,
    r.source.hint, r.source.modulus, r.source.arity, (toks r.source.formula).length]

/-- `lem:print`, paper/paper.tex: the whole original
compiler word has exactly its seven fields and original postfix bytes. -/
theorem FamilyCompileRequest.word_eq_header (r : FamilyCompileRequest) :
    r.word = r.header.flatMap natWord ++ tokenStream (toks r.source.formula) := by
  simp [FamilyCompileRequest.word, FamilyCompileRequest.header, ModFormulaRequest.word,
    formulaWord, NearCubicGates.Close.Interfaces.listWord, tokenStream, List.append_assoc]

/-- `lem:print`, paper/paper.tex: every metadata field
is decoded by the checked physical natural-field reader. -/
def familyHeaderProgram : St VV MM := StageGamma.readFields familyHeaderVars

/-- `lem:print`, paper/paper.tex: actual source parsing
leaves its head exactly at the original Formula tokens and retains all
previous physical stores and buffers. -/
theorem familyHeaderProgram_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (r : FamilyCompileRequest) (hin : C.inp.drop a.ip = r.word)
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
    (tokenStream (toks r.source.formula)) (by rw [← r.word_eq_header]; exact hin) hwidth).mono le_rfl ?_
  rintro b ⟨hv, hi, hr, hbc, hf⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hi, hr, hbc, hf⟩
  · simpa [familyHeaderVars, FamilyCompileRequest.header] using hv ⟨1, by decide⟩
  · simpa [familyHeaderVars, FamilyCompileRequest.header] using hv ⟨5, by decide⟩
  · simpa [familyHeaderVars, FamilyCompileRequest.header] using hv ⟨0, by decide⟩
  · simpa [familyHeaderVars, FamilyCompileRequest.header] using hv ⟨3, by decide⟩
  · simpa [familyHeaderVars, FamilyCompileRequest.header] using hv ⟨4, by decide⟩
  · simpa [familyHeaderVars, FamilyCompileRequest.header] using hv ⟨6, by decide⟩
  · simpa [familyHeaderVars, FamilyCompileRequest.header] using hv ⟨2, by decide⟩

/-- `prop:time`, paper/paper.tex: the small structural
hint covers the complete numeric family-field width and original arity. -/
theorem FamilyCompileRequest.setupHint_width (r : FamilyCompileRequest) :
    r.family.width + 2 ≤ r.setupHint := by
  have hh : r.degree + r.source.arity + 10 ≤ (r.degree + r.source.arity + 10) ^ 2 :=
    Nat.le_self_pow (by norm_num) _
  dsimp [FamilyCompileRequest.family, FamilyRequest.width, FamilyCompileRequest.setupHint]
  omega

end NearQuarticWires.StageRecovery
