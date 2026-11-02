import Proof.Quartic.StageLift.SourcePacket
import Proof.Quartic.StageRecovery.TermsMachine

set_option autoImplicit false

namespace NearQuarticWires.StagePrint.TermsCarrier

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats

/-- `lem:residue` and `lem:print`, paper/paper.tex: the actual modular compiler expands the normalized
original walk Formula at its unchanged finite degree. -/
noncomputable def actualTerms {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2)
    (index : Fin (r.child.cellCall.seed.N^8)) : Terms (17*(Builder.allGates r.child.call).length) :=
  StageRecovery.boundedModTerms (StageLift.sourceWalkPacket r index).modulus
    (StageLift.reduceConstants (StageLift.sourceWalkPacket r index).modulus
      (StageLift.sourceWalkFormula r index)) (StageLift.sourceWalkPacket r index).degree

/-- `lem:print`, paper/paper.tex: one actual
walk keeps its original encoded index, degree and modulus followed
by the canonical finite signed Terms word, including zero coefficients. -/
noncomputable def entryWord {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2)
    (index : Fin (r.child.cellCall.seed.N^8)) : List Bool :=
  natWord index.val++natWord (StageLift.sourceWalkPacket r index).degree++
    natWord (StageLift.sourceWalkPacket r index).modulus++frame (termsWord (actualTerms r index))

/-- Step 3 and `lem:print`, paper/paper.tex: one preparation context and its real walk count
precede every actual compiled Terms entry in original low-first order. -/
noncomputable def word {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) : List Bool :=
  natWord (StageLift.preparedWordOf r).length++StageLift.preparedWordOf r++
    natWord (r.child.cellCall.seed.N^8)++(List.ofFn (entryWord r)).flatten

/-- Step 3 and `lem:print`, paper/paper.tex: the required actual machine begins with the literal
printer source, not with isolated packets, decoded Formulas or Terms. -/
abbrev Producer (B1 B2 : ℕ) :=
  (budget : Greedy.PrintRequest B1 B2→ℕ) ×
    WordFunction (Greedy.PrintRequest B1 B2) Greedy.printInput (fun r=>frame (word r)) budget

#check actualTerms
#check entryWord
#check word
#check Producer

end NearQuarticWires.StagePrint.TermsCarrier
