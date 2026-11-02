import Proof.Quartic.StageFormulaMetadata.TokenStats
import Proof.Quartic.StageRecovery.FamilySource

set_option autoImplicit false

namespace NearQuarticWires.StageFormulaMetadata

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Expand
open StageRecovery (tokenStream)

/-- `lem:print`, paper/paper.tex: exact constants
and modular constants share the original raw postfix packet codec. -/
def validMode (modulus : ℕ) : Prop := modulus = 0 ∨ 2 ≤ modulus

/-- `lem:print`, paper/paper.tex: source validity
is a proof about physically printed bytes and their finite degree,
without a decoded formula or metadata field on the input tape. -/
def RawWalkPacket.Valid (packet : RawWalkPacket) : Prop :=
  ∃ formula : Formula packet.arity,
    packet.payload=tokenStream (toks formula) ∧
    formula.degree≤packet.degree ∧ validMode packet.modulus

/-- `lem:print`, paper/paper.tex: the source
emitter certifies its actual raw packet; validity carries no bytes. -/
def ValidPacket := {packet : RawWalkPacket // packet.Valid}

/-- `lem:print`, paper/paper.tex: the emitted
payload is the original seven-token codec after constant reduction. -/
def normalizedPayload (modulus : ℕ) (tokens : List Tok) : List Bool :=
  tokenStream (normalizeTokens modulus tokens)

/-- `lem:print`, paper/paper.tex: the inner
formula request has the actual arity, token count and emitted bytes. -/
def countedFormulaWord (arity modulus : ℕ) (tokens : List Tok) : List Bool :=
  natWord arity ++ natWord tokens.length ++ normalizedPayload modulus tokens

/-- `prop:time`, paper/paper.tex: the inner
workspace hint is computed from actual syntax and codec counters. -/
def countedHint (arity modulus : ℕ) (tokens : List Tok) : ℕ :=
  (arity+(tokens.map tokenAstSize).sum+(countedFormulaWord arity modulus tokens).length+
    natBitLength modulus+10)^2

/-- `lem:print`, paper/paper.tex: the complete
indexed request preserves the existing modular family byte order. -/
def formattedWord (index degree arity modulus : ℕ) (tokens : List Tok) : List Bool :=
  let hint := countedHint arity modulus tokens
  natWord index ++ natWord (hint+(degree+arity+10)^2) ++ natWord degree ++
    natWord (normalizedPayload modulus tokens).length ++ natWord hint ++
    natWord modulus ++ countedFormulaWord arity modulus tokens

/-- `lem:print`, paper/paper.tex: physically
counted formula bytes agree with the unchanged compiler codec. -/
theorem countedFormulaWord_toks {arity : ℕ} (modulus : ℕ) (formula : Formula arity) :
    countedFormulaWord arity modulus (toks formula)=
      formulaWord ⟨arity,StageLift.reduceConstants modulus formula⟩ := by
  simp only [countedFormulaWord,normalizedPayload,normalizeTokens_toks,
    formulaWord,NearCubicGates.Close.Interfaces.listWord,
    StageLift.reduceConstants_token_count,tokenStream,List.append_assoc]

/-- `prop:time`, paper/paper.tex: the computed
hint is exactly the compiler's sufficient structural hint. -/
theorem countedHint_toks {arity : ℕ} (modulus : ℕ) (formula : Formula arity) :
    countedHint arity modulus (toks formula)=
      (arity+(StageLift.reduceConstants modulus formula).size+
        (formulaWord ⟨arity,StageLift.reduceConstants modulus formula⟩).length+
        natBitLength modulus+10)^2 := by
  rw [countedHint,tokenAstSize_toks,countedFormulaWord_toks,
    StageLift.reduceConstants_size]

/-- `lem:print`, paper/paper.tex: a valid modular
packet supplies the compiler's original mathematical request, using
the normalized actual formula and the computed hint. -/
def modularFamily {arity : ℕ} (modulus degree : ℕ) (formula : Formula arity)
    (hq : 2 ≤ modulus) (hdegree : formula.degree ≤ degree) : StageRecovery.FamilyCompileRequest where
  source := {
    arity:=arity
    formula:=StageLift.reduceConstants modulus formula
    modulus:=modulus
    hint:=countedHint arity modulus (toks formula)
    modulus_ge_two:=hq
    hint_sufficient:=by rw [countedHint_toks] }
  degree:=degree
  degree_bound:=by rwa [StageLift.reduceConstants_degree]

/-- `lem:print`, paper/paper.tex: the modular
formatter's literal output is the unchanged indexed family request. -/
theorem formattedWord_modular {arity : ℕ} (index modulus degree : ℕ)
    (formula : Formula arity) (hq : 2 ≤ modulus) (hdegree : formula.degree ≤ degree) :
    formattedWord index degree arity modulus (toks formula)=
      natWord index ++ (modularFamily modulus degree formula hq hdegree).word := by
  simp only [formattedWord,StageRecovery.FamilyCompileRequest.word,
    StageRecovery.FamilyCompileRequest.setupHint,modularFamily,
    StageRecovery.ModFormulaRequest.word,normalizedPayload,normalizeTokens_toks,
    countedFormulaWord_toks,List.append_assoc]

/-- `lem:print`, paper/paper.tex: exact CERT
projects the original formula codec, retaining every signed constant
and avoiding a modulus-zero modular compiler request. -/
theorem countedFormulaWord_exact {arity : ℕ} (formula : Formula arity) :
    countedFormulaWord arity 0 (toks formula)=formulaWord ⟨arity,formula⟩ := by
  rw [countedFormulaWord_toks,reduceConstants_zero]

end NearQuarticWires.StageFormulaMetadata
