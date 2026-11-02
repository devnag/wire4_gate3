import Proof.Quartic.StageRecovery.ModFormulaBounds
import Proof.Quartic.StageGamma.ReadFields

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicWires NearCubicGates.Close.Cells NearCubicGates.Close.Expand
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Interfaces.Formats

/-- `lem:print`, paper/paper.tex: one internal Boolean
characteristic point at which the original formula is evaluated. -/
structure ModPointRequest where
  source : ModFormulaRequest
  point : ℕ
  point_fit : point < 2 ^ source.arity

/-- `lem:print`, paper/paper.tex: the internal point
evaluator adds only the literal characteristic point to the formula
compiler request; no formula values or coefficients are supplied. -/
def ModPointRequest.word (r : ModPointRequest) : List Bool :=
  natWord r.source.hint ++ natWord r.source.modulus ++ natWord r.point ++
    formulaWord ⟨r.source.arity, r.source.formula⟩

/-- `lem:print`, paper/paper.tex: the original formula's
variable count is kept separately from the token count and work loops. -/
def arityVar : Fin VV := ⟨84, by decide⟩

/-- `lem:print`, paper/paper.tex: the exact five binary
header destinations of one internal modular formula evaluation. -/
def pointFields : List (Fin VV) :=
  [widthVar, modulusVar, pointVar, arityVar, tokenCountVar]

/-- `lem:print`, paper/paper.tex: the actual encoded
header values precede the unchanged literal postfix token stream. -/
def ModPointRequest.fields (r : ModPointRequest) : List ℕ :=
  [r.source.hint, r.source.modulus, r.point, r.source.arity, (toks r.source.formula).length]

/-- `lem:print`, paper/paper.tex: the internal point
request contains exactly its five ordinary natural fields and original
formula tokens in the existing byte order. -/
theorem ModPointRequest.word_eq (r : ModPointRequest) :
    r.word = r.fields.flatMap natWord ++ tokenStream (toks r.source.formula) := by
  simp [ModPointRequest.word, ModPointRequest.fields, formulaWord,
    NearCubicGates.Close.Interfaces.listWord, tokenStream, List.append_assoc]

/-- `lem:print`, paper/paper.tex: the existing physical
binary-field parser is applied to the exact finite point-evaluator header. -/
def pointFieldsProgram : St VV MM := StageGamma.readFields pointFields

/-- `lem:print`, paper/paper.tex: every internal point
header is read from its actual bytes, with the exact cursor at the first
original postfix token and all retained values in binary variables. -/
theorem pointFieldsProgram_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (r : ModPointRequest) (hin : C.inp.drop a.ip = r.word)
    (hwidth : ∀ value ∈ r.fields, natBitLength value + 2 ≤ C.Wd) :
    Hs C pointFieldsProgram a (StageGamma.readFieldsCost r.fields) (fun b =>
      b.env modulusVar = r.source.modulus ∧ b.env pointVar = r.point ∧
      b.env tokenCountVar = (toks r.source.formula).length ∧
      b.ip = a.ip + (r.fields.flatMap natWord).length ∧ b.out = a.out ∧ Cst b) := by
  refine (StageGamma.readFields_spec C pointFields (by decide) (by decide)
    r.fields (by simp [pointFields, ModPointRequest.fields]) a hc
    (tokenStream (toks r.source.formula)) (by rw [← r.word_eq]; exact hin) hwidth).mono le_rfl ?_
  rintro b ⟨hv, hi, hr, hbc, _⟩
  refine ⟨?_, ?_, ?_, hi, congrArg Prod.fst hr, hbc⟩
  · simpa [pointFields, ModPointRequest.fields] using hv ⟨1, by decide⟩
  · simpa [pointFields, ModPointRequest.fields] using hv ⟨2, by decide⟩
  · simpa [pointFields, ModPointRequest.fields] using hv ⟨4, by decide⟩

end NearQuarticWires.StageRecovery
