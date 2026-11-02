import Proof.Quartic.StagePrint.EntryReader
import Proof.Quartic.StagePrint.EntryAllocationTarget

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint.EntryFormat
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open StageRecovery.OutputFrame

/-- `lem:print`, paper/paper.tex: the actual
formatter starts from empty stores, reads its literal source, then
frames only the newly written eleven-field Tuple request. -/
def coldProgram (modular : Bool) : St VV MM :=
  .seq initP (.seq (readerProgram modular) (framedProgram writerProgram))

/-- `prop:time`, paper/paper.tex: the whole
formatter clock includes initialization, one complete source read and
every payload and marker bit in the existing Tuple word. -/
noncomputable def coldSteps {modular : Bool} (r : Request modular) : ℕ :=
  readerSteps r+3*writerSteps r+9

/-- `lem:print`, paper/paper.tex: a genuine
zero-state execution transforms the actual original-arity-first source
into the complete framed native Tuple request, with no decoded input
or source, count, row, width or length provider assumption. -/
theorem coldProgram_run {modular : Bool} (C : Ctx) (r : Request modular)
    (hin : C.inp=r.word) (hsize : r.sizingMagnitude+10≤C.Wd) :
    Hs C (coldProgram modular) (a0 : DS VV MM) (coldSteps r)
      (fun last=>last.out=frame r.termRequest.word) := by
  have hf:=inputFits_of_sizing C r hsize
  have htwo : 2<2^C.Wd :=
    lt_of_lt_of_le (by decide : 2<2^2) (Nat.pow_le_pow_right (by decide) hf.wordWidth)
  unfold coldProgram
  refine (Hs.seq (t1:=5) (t2:=readerSteps r+3*writerSteps r+3)
    (initP_spec (C:=C) (a0 : DS VV MM) rfl rfl rfl htwo)
    fun a ⟨hc,hram,hrc,hip,hout,_hkin,_hkout,_hkc,_hfr⟩=>?_).mono
      (by unfold coldSteps;omega) (fun _ h=>h)
  have hblank : ∀ s,a.ram s=[] ∧ a.rc s=0 := by
    intro s
    rw [hram,hrc]
    exact ⟨rfl,rfl⟩
  have hai : C.inp.drop a.ip=r.word := by rw [hip];simpa only [a0,List.drop_zero] using hin
  have hao : a.out=[] := by simpa only [a0] using hout
  refine (Hs.seq (t1:=readerSteps r) (t2:=3*writerSteps r+2)
    (readerProgram_run C r a hc hai hblank hf)
    fun b ⟨bReady,bo⟩=>?_).mono (by omega) (fun _ h=>h)
  obtain ⟨last,n,he,hn,hout⟩:=writerProgram_run C r b bReady hf.toFits
  have heframe:=framedProgram_spec he
  have bEmpty : b.out=[]:=bo.trans hao
  have hmark : markedState b=b := by
    unfold markedState markedBits
    simp only [bEmpty,List.flatMap_nil]
    rw [←bEmpty]
  rw [hmark] at heframe
  refine ⟨framedState last,3*n+2,heframe,by omega,?_⟩
  change frame last.out=frame r.termRequest.word
  rw [hout,bEmpty,List.nil_append]

/-- `prop:time`, paper/paper.tex: the ordinary
formatter's clock is the actual language compiler clock under its
fixed original-arity allocation, including input and memory resets. -/
noncomputable def allocatedBudget {C E : ℕ} {modular : Bool}
    (allocation : Allocation C E modular) (r : BoundedRequest C E modular) : ℕ :=
  langBudget StageRecovery.packetCallee allocation.sizes VV MM r.word (coldSteps r.toRequest)

/-- `lem:print` and `prop:time`, paper/paper.tex: an actual fixed ordinary formatter is obtained from
the proved original-arity allocation and the complete zero-state
source execution; no callee or native-table algorithm is a premise. -/
noncomputable def formatterWithAllocation {C E : ℕ} {modular : Bool}
    (allocation : Allocation C E modular) :
    WordFunction (BoundedRequest C E modular) BoundedRequest.word
      (fun r=>frame r.toRequest.termRequest.word) (allocatedBudget allocation) :=
  wordFunction_of_lang BoundedRequest.word (fun r=>frame r.toRequest.termRequest.word)
    StageRecovery.packetCallee allocation.sizes (coldProgram modular)
    (fun r=>coldSteps r.toRequest) (by
      intro r
      obtain ⟨last,n,he,hn,hout⟩:=coldProgram_run
        (ctxOf StageRecovery.packetCallee allocation.sizes r.word) r.toRequest rfl
        (allocation.required r)
      exact ⟨last,n,he,hout,hn⟩) (by
      intro r
      have h:=allocation.required r
      omega)

end NearQuarticWires.StagePrint.EntryFormat
