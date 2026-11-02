import Proof.Quartic.StagePrintTuple.RecordField
import Proof.Quartic.StagePrintTuple.MarkedFrame
import Proof.Quartic.StagePrintTuple.UnaryHeaders
import Proof.Quartic.StagePrintTuple.RecordOutputs

set_option autoImplicit false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms.SInt (encS)

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual Stack source size counts its native tuple
bytes, fixed-width constants and four computed unary dimensions. -/
def stackInputMagnitude (r : StagePrint.StackRequest) : ℕ :=
  ((fieldRecords (r.W+1) (r.tuples.map List.flatten)).flatMap frame).length+
    r.W+r.m*(r.s+1)+(r.s+1)+r.m+r.tuples.length+10

/-- `lem:print`, paper/paper.tex: the exact
physical Stack formatter reads its current tuple segment and genuine
cached fixed-width fields, retaining all computed dimension registers. -/
abbrev StackInputSpec {ns nr : ℕ}
    (program : (Fin 5 ↪ Fin (ns+1))→(Fin 8 ↪ Fin nr)→WM ns nr) : Prop :=
  ∀ (cap : ℕ) (P : Fin 5 ↪ Fin (ns+1)) (R : Fin 8 ↪ Fin nr) (r : StagePrint.StackRequest)
    (pre : List Bool) (σ : WState ns nr),
    σ.st (P 0)=pre++(fieldRecords (r.W+1) (r.tuples.map List.flatten)).flatMap frame++[false] →
    σ.sh (P 0)=pre.length →
    σ.st (P 1)=frame (frame (binary (r.W+1) 0)) →
    σ.st (P 2)=frame (frame (binary (r.W+1) (encS r.coefficient))) →
    σ.st (P 3)=frame (frame (binary (r.W+1) 2)) →
    (∀ i : Fin 4,σ.sh (P (Fin.succ i))=0) → σ.st (P 4)=[] →
    (∀ i : Fin 4,σ.val (R (Fin.castAdd 4 i))=0) →
    [R 4,R 5,R 6,R 7].map σ.val=[r.m*(r.s+1),r.s+1,r.m,r.tuples.length] →
    400*stackInputMagnitude r≤cap →
    WExec cap (program P R) σ (σ.sets (P 4) (frame r.word)) (10000*stackInputMagnitude r)

end NearQuarticWires.StageTuple
