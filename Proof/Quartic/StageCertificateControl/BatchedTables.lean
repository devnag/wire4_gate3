import Proof.Quartic.StageCertificateControl.CountAvoid
import Proof.Quartic.StageCertificateControl.PoolFlattenRun

/-!
# One complete counted batch of native certificate tables

Paper: Step 2 of `sec:algorithm`, paper/paper.tex,
`lem:print`, and `prop:time`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close NearCubicGates.Close.Interfaces NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.CheckedPCPP
open NearQuarticWires.Control

/-- `sec:algorithm` and `prop:time`, paper/paper.tex: the true count computation precedes the existing
whole-table loop and one complete payload-flattening pass. -/
noncomputable def batchedTablesProgram (p q : Program) (hq : q.tapeCount≤p.tapeCount) :
    WMX (p.tapeCount+5) 16 :=
  .seq (poolCountProgram p q hq)
    (.seq (StagePrint.poolLoopProgram p) (flattenPoolProgram p))

/-- `prop:time`, paper/paper.tex: the common
capacity is the sum of literal bootstrap, native-loop and final-copy
requirements, including every cached native byte. -/
def batchedTablesCapacity {I : Type} {indexedInput : I→List Bool}
    (F : StagePrint.PoolFamily I indexedInput) (payload : I→List Bool) (budget : I→ℕ)
    (countBudget : ℕ) : ℕ :=
  4*F.source.length+4+(2*F.source.length+2+countBudget)+
    (2^(natBitLength F.count+1)+F.count+4*natBitLength F.count+4)+
    F.capacity payload budget+
    flattenPoolCapacity F.source.length (StagePrint.poolPrefix (F.caches payload) F.count).length F.count

/-- `prop:time`, paper/paper.tex: the complete
batch clock is a sum of actual count work, every indexed native-table
call and one linear scan over the accumulated native bytes. -/
def batchedTablesCost {I : Type} {indexedInput : I→List Bool}
    (F : StagePrint.PoolFamily I indexedInput) (payload : I→List Bool) (budget : I→ℕ)
    (countBudget : ℕ) : ℕ :=
  poolCountCost F.source.length countBudget F.count+F.loopBudget budget+
    flattenPoolCost F.source.length (StagePrint.poolPrefix (F.caches payload) F.count).length F.count+2

/-- `sec:algorithm`, `lem:print`, and `prop:time`, paper/paper.tex: a cold original preparation
is retained once, its exact census is computed, every whole native
table is called on its literal indexed input, and the final frame contains
the preparation, actual census, and all unchanged native payloads. -/
theorem batchedTables_exec {Request I : Type} {source : Request→List Bool}
    {count countBudget : Request→ℕ} {indexedInput payload : I→List Bool} {budget : I→ℕ}
    (counter : WordFunction Request source
      (fun r => frame (RepairRepresentation.natWord (count r))) countBudget)
    (provider : WordFunction I indexedInput (fun i => frame (payload i)) budget)
    (hq : counter.program.tapeCount≤provider.program.tapeCount)
    (req : Request) (F : StagePrint.PoolFamily I indexedInput)
    (hsource : F.source=source req) (hcount : F.count=count req) :
    ∃ τ, WXExec (batchedTablesCapacity F payload budget (countBudget req))
      (batchedTablesProgram provider.program counter.program hq)
      (startState (provider.program.tapeCount+5) 16 (source req)) τ
      (batchedTablesCost F payload budget (countBudget req)) ∧
      τ.st (StagePrint.poolFinal provider.program)=
        frame (flattenedPoolWord F.source (F.caches payload) F.count) := by
  let cap := batchedTablesCapacity F payload budget (countBudget req)
  have parts (a b c d e : ℕ) : a≤a+b+c+d+e ∧ b≤a+b+c+d+e ∧
      c≤a+b+c+d+e ∧ d≤a+b+c+d+e ∧ e≤a+b+c+d+e := by omega
  obtain ⟨hcopy,hcall,hheader,hpool,hflat⟩ := parts
    (4*F.source.length+4) (2*F.source.length+2+countBudget req)
    (2^(natBitLength F.count+1)+F.count+4*natBitLength F.count+4)
    (F.capacity payload budget)
    (flattenPoolCapacity F.source.length (StagePrint.poolPrefix (F.caches payload) F.count).length F.count)
  change 4*F.source.length+4≤cap at hcopy
  change 2*F.source.length+2+countBudget req≤cap at hcall
  change 2^(natBitLength F.count+1)+F.count+4*natBitLength F.count+4≤cap at hheader
  change F.capacity payload budget≤cap at hpool
  change flattenPoolCapacity F.source.length
    (StagePrint.poolPrefix (F.caches payload) F.count).length F.count≤cap at hflat
  rw [hsource] at hcopy hcall
  rw [hcount] at hheader
  obtain ⟨a,ec,hc⟩ := poolCount_exec counter provider.program hq req (F.caches payload) cap hcopy hcall hheader
  rw [← hsource,← hcount] at hc
  obtain ⟨b,el,hl⟩ := StagePrint.poolLoop_exec provider F
  obtain ⟨bActual,elActual,hlActual⟩ := wxexec_sim (word_capacity el hpool) a hc
  have hsim : SimW (StagePrint.poolState provider.program F.source (F.caches payload) F.count 0) bActual :=
    SimW.trans hl hlActual
  have freshCount := Control.WXExec.avoids ec (poolCount_avoids_final provider.program counter.program hq)
  have freshLoop := Control.WXExec.avoids elActual (StagePrint.poolLoop_avoids provider.program)
  have hfresh : bActual.st (StagePrint.poolFinal provider.program)=[] := by
    rw [freshLoop.1,freshCount.1]
    simp [startState,StagePrint.poolFinal]
  have hhead : bActual.sh (StagePrint.poolFinal provider.program)=0 := by
    rw [freshLoop.2,freshCount.2]
    rfl
  obtain ⟨τ,ef,hout⟩ := flattenPool_run provider.program cap F.source (F.caches payload) F.count
    bActual hsim hfresh hhead hflat
  refine ⟨τ,(ec.seq (elActual.seq ef)).mono ?_,hout⟩
  unfold batchedTablesCost
  rw [← hsource,← hcount]
  omega

end NearQuarticWires.StageCertificateControl
