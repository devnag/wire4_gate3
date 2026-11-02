import Proof.Quartic.StagePrintTuple.SetupContract

set_option autoImplicit false

namespace NearQuarticWires.StageTupleSetup

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.Interfaces
open StageTuple

/-- `prop:time`, paper/paper.tex: final preparation
copies full source bytes only linearly; its separate structural size
contains no Terms or Terms length. -/
def preparedOutputMagnitude (r : TermCutRequest) : ℕ :=
  r.word.length+r.setupStructuralMagnitude

/-- `lem:print`, paper/paper.tex: the actual full
prepared11field formatter reads original retained sources and genuine
small helper replies. It restores all source heads/scratch and copies
Terms exactly once through its actual existing outer-field frame. -/
abbrev PreparedOutputSpec {ns nr : ℕ}
    (program : (Fin 10↪Fin (ns+1))→(Fin 4↪Fin nr)→WM ns nr) : Prop :=
  ∀(cap : ℕ)(P : Fin 10↪Fin (ns+1))(R : Fin 4↪Fin nr)
    (r : TermCutRequest)(σ : WState ns nr),
    σ.st (P 0)=frame (callWord r.header.call) →
    σ.st (P 1)=frame ((StagePrint.Header.baseHeaderValues r.header).flatMap natWord) →
    σ.st (P 2)=frame r.contextWord →
    σ.st (P 3)=r.word →
    σ.st (P 4)=frame (natWord (r.stackWidth+1)) →
    σ.st (P 5)=(CoefficientRequest.mk (r.stackWidth+1) 0).output →
    σ.st (P 6)=(CoefficientRequest.mk (r.stackWidth+1) 1).output →
    σ.st (P 7)=frame (natWord (r.rowDimension+1)) →
    σ.st (P 8)=frame (natWord r.degree) →
    σ.st (P 9)=[] →
    (∀i,σ.sh (P i)=0) → (∀i,σ.val (R i)=0) →
    1000*preparedOutputMagnitude r≤cap →
    WExec cap (program P R) σ (σ.sets (P 9) (frame r.preparedWord))
      (100000*preparedOutputMagnitude r)

end NearQuarticWires.StageTupleSetup
