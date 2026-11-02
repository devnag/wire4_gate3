import Proof.Quartic.StageRecovery.ModSubtraction

set_option autoImplicit false

namespace NearQuarticWires.StageRecovery

open NearCubicGates.Close.Cells

/-- `lem:print`, paper/paper.tex: the characteristic
Boolean assignment used for the bounded coefficient evaluation. -/
def pointVar : Fin VV := ⟨78, by decide⟩
/-- `lem:print`, paper/paper.tex: the decoded original
atom index of a variable token. -/
def atomVar : Fin VV := ⟨79, by decide⟩
/-- `lem:print`, paper/paper.tex: the literal postfix
operation tag, independent of arithmetic work variables. -/
def tagVar : Fin VV := ⟨80, by decide⟩
/-- `lem:print`, paper/paper.tex: the count of literal
postfix tokens in the formula codec. -/
def tokenCountVar : Fin VV := ⟨81, by decide⟩
/-- `lem:print`, paper/paper.tex: the sequential formula
token counter, independent of the power loop counter. -/
def tokenCounterVar : Fin VV := ⟨82, by decide⟩

/-- `lem:print`, paper/paper.tex: the complete finite
set of variables that one postfix token may modify. -/
def evalScratch : List (Fin VV) :=
  [stackVar, leftVar, rightVar, productVar, quotientVar, remainderVar, c0,
    signVar, exponentVar, atomVar, tagVar, t0, t1, t2, t3, t4, vJ]

end NearQuarticWires.StageRecovery
