import Proof.Quartic.StageFormulaMetadata.ReadCountedNatural
import Proof.Quartic.StageFormulaMetadata.ConstantNormalize
import Proof.Quartic.StageRecovery.ModDispatch

set_option autoImplicit false

namespace NearQuarticWires.StageFormulaMetadata

open NearCubicGates.Close.Cells
open StageRecovery

/-- `lem:print`, paper/paper.tex: the token and
syntax-size counters are distinct from all coefficient arithmetic. -/
def countedTokensVar : Fin VV := 89
def syntaxSizeVar : Fin VV := 90

/-- `lem:print`, paper/paper.tex: an actual
constant token is decoded, normalized in the selected mode, counted
and optionally emitted with its original signed-integer codec. -/
def constantPayload (printing : Bool) : St VV MM :=
  .seq (readTrackedNatural 0 signVar)
    (.seq (readTrackedNatural 0 leftVar)
      (.seq normalizeConstant
        (.seq (countedNatural printing signVar) (countedNatural printing leftVar))))

/-- `lem:print`, paper/paper.tex: atom indices
are decoded and copied without changing the original variable roles. -/
def variablePayload (printing : Bool) : St VV MM :=
  readCountedNatural printing atomVar

/-- `lem:print` and `prop:time`, paper/paper.tex: a power adds its binary exponent to the syntax-size
counter in one bounded addition, without iterating over the exponent. -/
def powerPayload (printing : Bool) : St VV MM :=
  .seq (readCountedNatural printing exponentVar) (.op (.add syntaxSizeVar exponentVar))

/-- `lem:print`, paper/paper.tex: the existing
seven-tag postfix order is shared by the counting and output passes. -/
def metadataHandlers (printing : Bool) : List (St VV MM) :=
  [constantPayload printing,variablePayload printing,skipS,skipS,skipS,skipS,powerPayload printing]

/-- `lem:print`, paper/paper.tex: one actual
token tag is read and counted before updating both syntax counters. -/
def metadataHead (printing : Bool) : St VV MM :=
  .seq (readCountedNatural printing tagVar)
    (.seq (.op (.inc countedTokensVar))
      (.op (.inc syntaxSizeVar)))

/-- `lem:print`, paper/paper.tex: one actual
token advances the source-byte counter, counts its tag and syntax
node, then executes its literal payload handler. -/
def metadataToken (printing : Bool) : St VV MM :=
  .seq (metadataHead printing) (tokenDispatch (metadataHandlers printing))

end NearQuarticWires.StageFormulaMetadata
