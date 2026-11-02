import Proof.Quartic.StageCertTests.MemoryCallKind
import Proof.Quartic.StageCertTests.WholeSchedule
import Proof.Gates.Cells.Prelude

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertTests

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces

/-- `sec:algorithm`, paper/paper.tex:
the complete schedule is generated directly from the original
successful preparation source, without an extra supplied header. -/
def prepScheduleProgram : St VV MM :=
  .seq initP (.seq StageLift.readCallSource (.seq readRetainedCallKind
    (.seq StageLift.readParameters (.seq (loadScheduleFields scheduleFields) wholeSchedule))))

/-- `prop:time`, paper/paper.tex:
the exact direct-source clock pays original-call acquisition,
its kind-field head return, all parameter decoding and every test request. -/
def prepScheduleSteps (c : Call) (p : Cells.Parameters) : ℕ :=
  5+((3000*((callWord c).length+1)^3+12*(callWord c).length+16)+
    (((callWord c).length+30*natBitLength c.n+30*natBitLength (kindTag c.kind)+67)+
      (StageLift.parameterReadCost p (scheduleHint p)+(761+wholeScheduleSteps p (scheduleHint p)+1)+1)+1)+1)+1

/-- `sec:params`, `sec:algorithm` and `prop:time`, paper/paper.tex: a true original
preparation prefix physically produces the entire exact test schedule,
with its arbitrary following witness suffix left unread. -/
theorem prepScheduleProgram_spec (C : Ctx) (c : Call) (p : Cells.Parameters) (rest : List Bool)
    (hin : C.inp = true :: (callWord c ++ Program.parametersWord p ++ rest))
    (hcall : (callWord c).length+2 ≤ C.Wd) (hwidth : 64*(scheduleHint p+1) ≤ C.Wd) :
    Hs C prepScheduleProgram (a0 : DS VV MM) (prepScheduleSteps c p)
      (fun b => b.out = (certificateMetadata p c.kind).flatMap TestMetadata.word) := by
  have bounds := scheduleBounds_of_width C p hwidth
  have hlarge := bounds.large
  have htagbits : natBitLength (kindTag c.kind) ≤ 2 := by cases c.kind <;> decide
  have hnword : (natWord c.n).length ≤ (callWord c).length := by simp [callWord]
  have hnwidth : natBitLength c.n+2 ≤ C.Wd := by rw [natWord_length] at hnword;omega
  unfold prepScheduleProgram prepScheduleSteps
  refine Hs.seq (initP_spec (C := C) (a0 : DS VV MM) rfl rfl rfl (by have := bounds.small;omega))
    fun a ⟨hac,harm,harc,hai,hao,_,_,_,_⟩ => ?_
  have haf : C.inp.drop a.ip = true :: (callWord c ++ (Program.parametersWord p ++ rest)) := by
    rw [hai]
    simpa only [a0,List.drop_zero,List.append_assoc] using hin
  refine Hs.seq (StageLift.readCallSource_spec C c (Program.parametersWord p ++ rest) a hac haf hcall
    (by rw [harm,harc];exact ⟨rfl,rfl⟩))
    fun b ⟨hbi,_,hbcall,hbcallc,hbother,hbsh,hbc,_⟩ => ?_
  have hbin : C.inp.drop b.ip = Program.parametersWord p ++ rest := by
    rw [hbi,hai]
    simp only [a0,Nat.zero_add]
    rw [hin]
    rw [Nat.add_comm 1 (callWord c).length]
    simp only [List.drop_succ_cons,List.append_assoc,List.drop_left]
  have hread := readRetainedCallKind_spec C b c hbc hbcall hnwidth (by omega)
  rw [hbcallc] at hread
  refine Hs.seq hread fun d ⟨hdk,hdrest,_,hdc,_⟩ => ?_
  have hdi : d.ip = b.ip := congrArg Prod.fst hdrest
  have hdram : d.ram = b.ram := congrArg (fun q => q.2.2.1) hdrest
  have hdempty : ∀ store ∈ [StageLift.parameterStore,StageLift.primeStore,StageLift.factorStore],
      d.ram store = [] ∧ d.rc store = 0 := by
    intro store hs
    have hne : store ≠ StageLift.callStore := by
      rcases (by simpa only [List.mem_cons,List.not_mem_nil,or_false] using hs) with
        rfl | rfl | rfl <;> decide
    have hdrc : d.rc store = b.rc store := by
      have hh := congrArg (fun q => q.2.2.2.1 store) hdrest
      simpa only [StageLift.memorySourceRest,Function.update_of_ne hne] using hh
    rw [hdram,hdrc,(hbother store hne).1,(hbother store hne).2,harm,harc]
    exact ⟨rfl,rfl⟩
  refine Hs.seq (StageLift.readParameters_cursor_spec C p (scheduleHint p) rest d hdc
    (by rw [hdi];exact hbin) bounds.parserBits (by omega) bounds.parserCounts hdempty)
    fun e ⟨⟨_,hep,_,_,_,_,hesh,hec,hefr⟩,herc,_,_⟩ => ?_
  have hek : e.env scheduleCallKindVar = kindTag c.kind := by rw [hefr _ (by decide),hdk]
  refine Hs.seq (loadAllScheduleFields_spec C e p hep (by omega) hec)
    fun f ⟨hfields,_,hfrest,hfc,hffr⟩ => ?_
  have hfk : f.env scheduleCallKindVar = kindTag c.kind := by rw [hffr _ (by decide),hek]
  refine (wholeSchedule_spec C f p c.kind (scheduleHint p) hfc hfields hfk bounds).mono le_rfl ?_
  rintro g ⟨hgo,_,_⟩
  have hfo : f.out = e.out := congrArg (fun q => q.2.1) hfrest
  have heo : e.out = d.out := congrArg Prod.fst hesh
  have hdo : d.out = b.out := congrArg (fun q => q.2.1) hdrest
  have hbo : b.out = a.out := congrArg Prod.fst hbsh
  rw [hgo,hfo,heo,hdo,hbo,hao]
  rfl

end NearQuarticWires.StageCertTests
