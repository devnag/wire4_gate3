import Proof.Gates.CounterAsm.Copy
import Proof.Quartic.StageFormulaMetadata.Packet
import Proof.Gates.Interfaces.CounterFormats

set_option autoImplicit false

namespace NearQuarticWires.StagePrint.PacketInterface
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Interfaces.Formats

/-- `lem:print`, paper/paper.tex: isolation measures one actual packet while leaving every following source byte unread. -/
def IsolationSpec {ns nr : ℕ}
    (program : (src dst : Fin (ns+1)) → (OP SC LEN K TMP : Fin nr) → WM ns nr) : Prop :=
  ∀ (cap : ℕ) (src dst : Fin (ns+1)) (OP SC LEN K TMP : Fin nr),src≠dst →
    [OP,SC,LEN,K,TMP].Nodup →
    ∀ (packet : StageFormulaMetadata.RawWalkPacket) (pre suffix : List Bool) (σ : WState ns nr),
    σ.st src=pre++packet.word++suffix → σ.sh src=pre.length →
    σ.st dst=[] → σ.sh dst=0 → σ.val OP=0 → σ.val SC=pre.length →
    σ.val LEN=0 → σ.val K=0 → σ.val TMP=0 →
    σ.val SC+4*packet.word.length+20≤ cap →
    ∃ τ,WExec cap (program src dst OP SC LEN K TMP) σ τ (100*(packet.word.length+1)) ∧
      τ.st src=σ.st src ∧ τ.sh src=pre.length+packet.word.length ∧
      τ.st dst=frame packet.word ∧ τ.sh dst=(frame packet.word).length ∧
      τ.val LEN=packet.word.length ∧ τ.val SC=pre.length+packet.word.length ∧
      τ.val OP=(frame packet.word).length ∧ τ.val K=0 ∧ τ.val TMP=0 ∧
      (∀ i,i≠src → i≠dst → τ.st i=σ.st i ∧ τ.sh i=σ.sh i) ∧
      (∀ r,r∉[OP,SC,LEN,K,TMP] → τ.val r=σ.val r) ∧ τ.cell=σ.cell

/-- `lem:print`, paper/paper.tex: the exact-CERT branch projects the original Formula codec after its six actual indexed fields. -/
structure ExactProjectionRequest where
  index : ℕ
  setupHint : ℕ
  degree : ℕ
  hint : ℕ
  formula : FormulaReq

/-- `lem:print`, paper/paper.tex: the fourth field is the actual signed postfix byte count, not a separately supplied source length. -/
def ExactProjectionRequest.payload (r : ExactProjectionRequest) : List Bool :=
  (toks r.formula.2).flatMap tokWord

def ExactProjectionRequest.word (r : ExactProjectionRequest) : List Bool :=
  natWord r.index++natWord r.setupHint++natWord r.degree++natWord r.payload.length++
    natWord r.hint++natWord 0++formulaWord r.formula

/-- `lem:print`, paper/paper.tex: projection retains the encoded index without a unary loop in its numeric magnitude, measures actual consumption and emits exactly the signed Formula request. -/
def ProjectionSpec {ns nr : ℕ}
    (program : (src dst idx : Fin (ns+1)) → (R : Fin 16 ↪ Fin nr) → WM ns nr) : Prop :=
  ∀ (cap : ℕ) (src dst idx : Fin (ns+1)) (R : Fin 16 ↪ Fin nr),[src,dst,idx].Nodup →
    ∀ (r : ExactProjectionRequest) (pre suffix : List Bool) (σ : WState ns nr),
    σ.st src=pre++r.word++suffix → σ.sh src=pre.length →
    σ.st dst=[] → σ.sh dst=0 → σ.st idx=[] → σ.sh idx=0 →
    σ.val (R 1)=pre.length → (∀ j : Fin 16,j≠1 → σ.val (R j)=0) →
    σ.val (R 1)+4*r.word.length+20≤ cap →
    ∃ τ,WExec cap (program src dst idx R) σ τ (100000*(r.word.length+1)^2) ∧
      τ.st src=σ.st src ∧ τ.sh src=pre.length+r.word.length ∧
      τ.st dst=frame (formulaWord r.formula) ∧ τ.sh dst=(frame (formulaWord r.formula)).length ∧
      τ.st idx=frame (natWord r.index) ∧ τ.sh idx=(frame (natWord r.index)).length ∧
      τ.val (R 0)=(frame (formulaWord r.formula)).length ∧
      τ.val (R 1)=pre.length+r.word.length ∧ τ.val (R 2)=r.word.length ∧
      τ.val (R 3)=(frame (natWord r.index)).length ∧
      (∀ j : Fin 16,j.val∉[0,1,2,3] → τ.val (R j)≤ 10*(r.word.length+1)) ∧
      (∀ i,i≠src → i≠dst → i≠idx → τ.st i=σ.st i ∧ τ.sh i=σ.sh i) ∧
      (∀ v,(∀ j,R j≠v) → τ.val v=σ.val v) ∧ τ.cell=σ.cell

#check (fun {ns nr : ℕ} (p : (src dst : Fin (ns+1)) → (OP SC LEN K TMP : Fin nr) → WM ns nr) => IsolationSpec p)
#check (fun {ns nr : ℕ} (p : (src dst idx : Fin (ns+1)) → (R : Fin 16 ↪ Fin nr) → WM ns nr) => ProjectionSpec p)

end NearQuarticWires.StagePrint.PacketInterface
