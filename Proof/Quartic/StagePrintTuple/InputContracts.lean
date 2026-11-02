import Proof.Quartic.StagePrintTuple.NestedField
import Proof.Quartic.StagePrintTuple.MarkedFrame
import Proof.Quartic.StagePrintTuple.SupportIndex
import Proof.Quartic.StagePrintTuple.PayloadAt

set_option autoImplicit false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.Interfaces

/-- `lem:print`, paper/paper.tex: an actual
native-pool cold input has its original call and header framed inside
the first two fields, followed by the unchanged context, atom and width. -/
def nativeKidsInputWord (call header context atom width : List Bool) : List Bool :=
  Top.loadRec (frame call) (frame header) context atom width [] [] [] [] [] []

/-- `prop:time`, paper/paper.tex: the actual
native-pool input source magnitude counts only its five finite fields. -/
def nativeKidsInputMagnitude (a b c d e : List Bool) : ℕ :=
  (frame a).length+(frame b).length+(frame c).length+(frame d).length+(frame e).length+10

/-- `lem:print`, paper/paper.tex: the exact
native-pool input formatter reads five genuine retained source frames
and emits the existing eleven-field request with all real delimiters. -/
abbrev NativeKidsInputSpec {ns nr : ℕ}
    (program : (Fin 6 ↪ Fin (ns+1))→(Fin 2 ↪ Fin nr)→WM ns nr) : Prop :=
  ∀ (cap : ℕ) (P : Fin 6 ↪ Fin (ns+1)) (R : Fin 2 ↪ Fin nr)
    (a b c d e : List Bool) (σ : WState ns nr),
    σ.st (P 0)=frame a → σ.st (P 1)=frame b → σ.st (P 2)=frame c →
    σ.st (P 3)=frame d → σ.st (P 4)=frame e → σ.st (P 5)=[] →
    (∀i,σ.sh (P i)=0) → (∀i,σ.val (R i)=0) →
    400*nativeKidsInputMagnitude a b c d e≤cap →
    WExec cap (program P R) σ (σ.sets (P 5) (frame (nativeKidsInputWord a b c d e)))
      (10000*nativeKidsInputMagnitude a b c d e)

/-- `prop:time`, paper/paper.tex: actual
support-index request formatting depends only on its one finite
support, computed index and computed support count. -/
def supportInputMagnitude (r : SupportIndexRequest) : ℕ :=
  r.support.length+r.index.val+(listWord natWord r.support).length+20

/-- `lem:print`, paper/paper.tex: the exact
support-index formatter consumes the physically parsed support cache
and persistent reverse-index/count registers, retaining every original
variable codec and all exterior state components. -/
abbrev SupportInputSpec {ns nr : ℕ}
    (program : (Fin 2 ↪ Fin (ns+1))→(Fin 9 ↪ Fin nr)→Fin nr→Fin nr→WM ns nr) : Prop :=
  ∀ (cap : ℕ) (P : Fin 2 ↪ Fin (ns+1)) (R : Fin 9 ↪ Fin nr) (J M : Fin nr)
    (r : SupportIndexRequest) (σ : WState ns nr),
    (∀i,R i≠J) → (∀i,R i≠M) →
    σ.st (P 0)=frame (listWord natWord r.support) →
    σ.sh (P 0)=(marks (natWord r.support.length)).length →
    σ.st (P 1)=[] → σ.sh (P 1)=0 → (∀i,σ.val (R i)=0) →
    σ.val J=r.index.val → σ.val M=r.support.length →
    1000*supportInputMagnitude r≤cap →
    WExec cap (program P R J M) σ (σ.sets (P 1) (frame r.word))
      (10000*(supportInputMagnitude r)^2)

end NearQuarticWires.StageTuple
