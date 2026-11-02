import Proof.Quartic.StageRecovery.ModFormulaBounds
import Proof.Quartic.StageRecovery.FamilyInput
import Proof.Quartic.StageRecovery.PacketRequest

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicWires
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Expand NearCubicGates.Close.Interfaces.Formats

/-- `lem:print`, paper/paper.tex: a literal modular
Formula and its serialized degree upper bound determine one complete
finite-family compiler request. -/
structure FamilyCompileRequest where
  source : ModFormulaRequest
  degree : ℕ
  degree_bound : source.formula.degree ≤ degree

/-- `prop:time`, paper/paper.tex: the compiler starts
with a structural clock magnitude, independent of support-family count,
walk index or any polynomial value. -/
def FamilyCompileRequest.setupHint (r : FamilyCompileRequest) : ℕ :=
  r.source.hint + (r.degree + r.source.arity + 10) ^ 2

/-- `lem:print`, paper/paper.tex: the exact original
postfix byte length is explicit paid metadata, preceding the unchanged
inner modular Formula codec. -/
def FamilyCompileRequest.word (r : FamilyCompileRequest) : List Bool :=
  natWord r.setupHint ++ natWord r.degree ++ natWord (tokenStream (toks r.source.formula)).length ++ r.source.word

/-- `lem:print`, paper/paper.tex: the actual family
request uses the original atom arity and the supplied finite degree bound. -/
def FamilyCompileRequest.family (r : FamilyCompileRequest) : FamilyRequest :=
  ⟨r.source.arity, r.degree⟩

/-- `prop:time`, paper/paper.tex: the cold setup word
starts with its small structural hint rather than an exponential index
or an already generated support-family count. -/
theorem FamilyCompileRequest.leading_hint (r : FamilyCompileRequest) :
    NearCubicGates.Close.Cells.leadOnes r.word = natBitLength r.setupHint := by
  unfold FamilyCompileRequest.word
  simpa only [List.append_assoc] using
    NearCubicGates.Close.CounterMachine.PrefixProg.leadOnes_natWord r.setupHint
      (natWord r.degree ++ natWord (tokenStream (toks r.source.formula)).length ++ r.source.word)

end NearQuarticWires.StageRecovery
