import Proof.Quartic.StageCertNative.PayloadOnly
import Proof.Quartic.StageCertNative.WeakPool

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close NearCubicGates.Close.CheckedPCPP
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Interfaces
open NearCubicGates.Close.Expand.PolyTab
open StageCertificateControl

/-- `lem:print`, paper/paper.tex: actual count,
term generation and one payload-only final scan form a whole source
program with no retained preparation bytes in the native cut stream. -/
noncomputable def payloadBatchProgram (p q : Program) (hq : q.tapeCount≤p.tapeCount) :
    WMX (p.tapeCount+5) 16 :=
  .seq (poolCountProgram p q hq)
    (.seq (StagePrint.poolLoopProgram p) (payloadOnlyProgram p))

def payloadBatchCost {I : Type} {input : I→List Bool} (F : StagePrint.PoolFamily I input)
    (payload : I→List Bool) (budget : I→ℕ) (countBudget : ℕ) : ℕ :=
  poolCountCost F.source.length countBudget F.count+F.loopBudget budget+
    1000*((StagePrint.poolPrefix (F.caches payload) F.count).length+F.count+1)+2

theorem payloadBatch_exec {Request I : Type} {source : Request→List Bool}
    {count countBudget : Request→ℕ} {input payload : I→List Bool} {budget : I→ℕ}
    (counter : WordFunction Request source (fun r=>frame (RepairRepresentation.natWord (count r))) countBudget)
    (provider : WordFunction I input (fun i=>frame (payload i)) budget)
    (hq : counter.program.tapeCount≤provider.program.tapeCount)
    (r : Request) (F : StagePrint.PoolFamily I input)
    (hsource : F.source=source r) (hcount : F.count=count r) :
    ∃τ,WXExec (batchedTablesCapacity F payload budget (countBudget r))
      (payloadBatchProgram provider.program counter.program hq)
      (startState (provider.program.tapeCount+5) 16 (source r)) τ
      (payloadBatchCost F payload budget (countBudget r)) ∧
      τ.st (StagePrint.poolFinal provider.program)=
        frame ((List.range F.count).flatMap (F.caches payload)) := by
  let cap:=batchedTablesCapacity F payload budget (countBudget r)
  have parts (a b c d e : ℕ) : a≤a+b+c+d+e ∧ b≤a+b+c+d+e ∧
      c≤a+b+c+d+e ∧ d≤a+b+c+d+e ∧ e≤a+b+c+d+e := by omega
  obtain ⟨hcopy,hcall,hheader,hpool,hflatFull⟩:=parts
    (4*F.source.length+4) (2*F.source.length+2+countBudget r)
    (2^(natBitLength F.count+1)+F.count+4*natBitLength F.count+4)
    (F.capacity payload budget)
    (flattenPoolCapacity F.source.length (StagePrint.poolPrefix (F.caches payload) F.count).length F.count)
  change 4*F.source.length+4≤cap at hcopy
  change 2*F.source.length+2+countBudget r≤cap at hcall
  change 2^(natBitLength F.count+1)+F.count+4*natBitLength F.count+4≤cap at hheader
  change F.capacity payload budget≤cap at hpool
  change 100*(F.source.length+(StagePrint.poolPrefix (F.caches payload) F.count).length+F.count+1)≤cap
    at hflatFull
  have hflat : 100*((StagePrint.poolPrefix (F.caches payload) F.count).length+F.count+1)≤cap := by
    exact (Nat.mul_le_mul_left 100 (by omega)).trans hflatFull
  rw [hsource] at hcopy hcall
  rw [hcount] at hheader
  obtain ⟨a,ec,hc⟩:=poolCount_exec counter provider.program hq r (F.caches payload)
    cap hcopy hcall hheader
  rw [←hsource,←hcount] at hc
  obtain ⟨b,el,hl⟩:=StagePrint.poolLoop_exec provider F
  obtain ⟨actual,er,hr⟩:=wxexec_sim (word_capacity el hpool) a hc
  have hsim : SimW (StagePrint.poolState provider.program F.source (F.caches payload) F.count 0) actual :=
    SimW.trans hl hr
  have hcountFresh:=Control.WXExec.avoids ec (poolCount_avoids_final provider.program counter.program hq)
  have hloopFresh:=Control.WXExec.avoids er (StagePrint.poolLoop_avoids provider.program)
  have ho : actual.st (StagePrint.poolFinal provider.program)=[] := by
    rw [hloopFresh.1,hcountFresh.1]
    simp [startState,StagePrint.poolFinal]
  have hh : actual.sh (StagePrint.poolFinal provider.program)=0 := by
    rw [hloopFresh.2,hcountFresh.2]
    rfl
  obtain ⟨last,ef,hf⟩:=payloadOnly_run provider.program cap F.source (F.caches payload)
    F.count actual hsim ho hh hflat
  refine ⟨last,(ec.seq (er.seq ef)).mono ?_,hf⟩
  unfold payloadBatchCost
  rw [←hsource,←hcount]
  omega

/-- `lem:print` and `prop:time`, paper/paper.tex: the exact whole finite cache stream is returned in
one frame after its counted actual computation; no source parser or
output-length value is required by the final concatenation. -/
noncomputable def payloadBatchWordFunction {Request I : Type}
    {source : Request→List Bool} {count countBudget : Request→ℕ}
    {input payload : I→List Bool} {budget : I→ℕ}
    (counter : WordFunction Request source (fun r=>frame (RepairRepresentation.natWord (count r))) countBudget)
    (provider : WordFunction I input (fun i=>frame (payload i)) budget)
    (hq : counter.program.tapeCount≤provider.program.tapeCount)
    (families : Request→StagePrint.PoolFamily I input)
    (hsource : ∀r,(families r).source=source r) (hcount : ∀r,(families r).count=count r) :
    WordFunction Request source
      (fun r=>frame ((List.range (families r).count).flatMap ((families r).caches payload)))
      (fun r=>2*payloadBatchCost (families r) payload budget (countBudget r)+2) :=
  wordFunction_of_ideal (payloadBatchProgram provider.program counter.program hq)
    (StagePrint.poolFinal provider.program) (by simp [StagePrint.poolFinal])
    (fun r=>batchedTablesCapacity (families r) payload budget (countBudget r)) (fun _ _=>0)
    (fun r=>payloadBatchCost (families r) payload budget (countBudget r))
    (fun _=>le_rfl) (by intro r;exact ⟨rfl,payloadBatch_exec counter provider hq r (families r)
      (hsource r) (hcount r)⟩)

end NearQuarticWires.StageCertNative
