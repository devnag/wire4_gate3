import Proof.Quartic.StageFormulaMetadata.WitnessDock

set_option autoImplicit false

namespace NearQuarticWires.StageFormulaMetadata

open NearCubicWires
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats
open StageRecovery (tokenStream)

/-- `lem:print`, paper/paper.tex: an actual
modular source emitter joins the unchanged indexed finite-family
compiler request using its own original Formula and degree proof. -/
theorem ValidPacket.output_modular (request : ValidPacket) (formula : Formula request.val.arity)
    (hsource : request.val.payload=tokenStream (toks formula))
    (hdegree : formula.degree≤request.val.degree) (hq : 2 ≤ request.val.modulus) :
    request.output=natWord request.val.index++
      (modularFamily request.val.modulus request.val.degree formula hq hdegree).word := by
  rw [request.output_of_source formula hsource]
  exact formattedWord_modular request.val.index request.val.modulus request.val.degree formula hq hdegree

/-- `lem:print`, paper/paper.tex: exact CERT
sources receive their original signed Formula codec after the six
actual outer fields, and never enter a modulus-zero modular compiler. -/
theorem ValidPacket.output_exact (request : ValidPacket) (formula : Formula request.val.arity)
    (hsource : request.val.payload=tokenStream (toks formula)) (hq : request.val.modulus=0) :
    let hint:=countedHint request.val.arity 0 (toks formula)
    request.output=natWord request.val.index++natWord (hint+(request.val.degree+request.val.arity+10)^2)++
      natWord request.val.degree++natWord (tokenStream (toks formula)).length++natWord hint++
      natWord 0++formulaWord ⟨request.val.arity,formula⟩ := by
  rw [request.output_of_source formula hsource]
  simp only [formattedWord,hq,normalizedPayload,normalizeTokens_zero,countedFormulaWord_exact,List.append_assoc]

end NearQuarticWires.StageFormulaMetadata
