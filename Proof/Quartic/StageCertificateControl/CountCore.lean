import Proof.Quartic.StageCertificateControl.TestCensus
import Proof.Quartic.StageCertTests.PrepScheduleSource
import Proof.Quartic.StageRecovery.NaturalPrint

/-!
# The actual preparation-to-test-count computation

Paper: Step 2 of `sec:algorithm`, paper/paper.tex,
and `prop:time`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces

/-- The whole-test loop bound of `sec:algorithm`, paper/paper.tex, is recovered from the actual call kind and public parameter
record. The witness frame and every following suffix remain unread. -/
def countCore : St VV MM :=
  .seq StageLift.readCallSource (.seq StageCertTests.readRetainedCallKind
    (.seq StageLift.readParameters (.seq (StageCertTests.loadScheduleFields StageCertTests.scheduleFields)
      (.seq setTestCensus (StageRecovery.emitVariable testCountVar)))))

/-- The exact scalar-count source clock in `prop:time`,
paper/paper.tex, pays the call scan and head
return, complete parameter decode, bounded arithmetic and real header output. -/
noncomputable def countCoreCost (c : Call) (p : Cells.Parameters) (B : ℕ) : ℕ :=
  (3000*((callWord c).length+1)^3+12*(callWord c).length+16)+
    (((callWord c).length+30*natBitLength c.n+30*natBitLength (kindTag c.kind)+67)+
      (StageLift.parameterReadCost p B+(761+
        (300+(40*natBitLength (StageCertTests.certificateMetadata p c.kind).length+42)+1)+1)+1)+1)+1

/-- The literal scalar-count computation of `sec:algorithm` and
`prop:time`, paper/paper.tex,
prints the exact complete scheduler count from original encoded data.
It does not inspect any witness or native table suffix and assumes no
predecoded kind, parameter, count or bitmap state. -/
theorem countCore_spec (C : Ctx) (c : Call) (p : Cells.Parameters) (rest : List Bool)
    (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip=true::(callWord c++Program.parametersWord p++rest))
    (hcall : (callWord c).length+2≤C.Wd)
    (hwidth : 64*(StageCertTests.scheduleHint p+1)≤C.Wd)
    (hempty : ∀ store,a.ram store=[] ∧ a.rc store=0) :
    Hs C countCore a (countCoreCost c p (StageCertTests.scheduleHint p)) (fun b =>
      b.out=a.out++natWord (StageCertTests.certificateMetadata p c.kind).length) := by
  have bounds := StageCertTests.scheduleBounds_of_width C p hwidth
  have hcounter := metadata_count_binary_bounds C p c.kind hwidth
  have htagbits : natBitLength (kindTag c.kind)≤2 := by cases c.kind <;> decide
  have hnword : (natWord c.n).length≤(callWord c).length := by simp [callWord]
  have hnwidth : natBitLength c.n+2≤C.Wd := by rw [natWord_length] at hnword;omega
  have hsmall := Nat.lt_two_pow_self (n := C.Wd)
  unfold countCore countCoreCost
  refine Hs.seq
    (StageLift.readCallSource_spec C c (Program.parametersWord p++rest) a hc
      (by simpa only [List.append_assoc] using hin) hcall (hempty _))
    fun b ⟨hbi,_,hbcall,hbcallc,hbother,hbs,hbc,_⟩ => ?_
  have hbin : C.inp.drop b.ip=Program.parametersWord p++rest := by
    rw [hbi,Nat.add_assoc,←List.drop_drop,hin,Nat.add_comm 1 (callWord c).length]
    simp only [List.drop_succ_cons,List.append_assoc,List.drop_left]
  have hread := StageCertTests.readRetainedCallKind_spec C b c hbc hbcall hnwidth (by have := bounds.width;omega)
  rw [hbcallc] at hread
  refine Hs.seq hread fun d ⟨hdk,hdrest,_,hdc,_⟩ => ?_
  have hdi : d.ip=b.ip := congrArg Prod.fst hdrest
  have hdram : d.ram=b.ram := congrArg (fun q => q.2.2.1) hdrest
  have hdempty : ∀ store∈[StageLift.parameterStore,StageLift.primeStore,StageLift.factorStore],
      d.ram store=[] ∧ d.rc store=0 := by
    intro store hs
    have hne : store≠StageLift.callStore := by
      rcases (by simpa only [List.mem_cons,List.not_mem_nil,or_false] using hs) with
        rfl|rfl|rfl <;> decide
    have hdrc : d.rc store=b.rc store := by
      have hh := congrArg (fun q => q.2.2.2.1 store) hdrest
      simpa only [StageLift.memorySourceRest,Function.update_of_ne hne] using hh
    rw [hdram,hdrc,(hbother store hne).1,(hbother store hne).2]
    exact hempty store
  refine Hs.seq
    (StageLift.readParameters_cursor_spec C p (StageCertTests.scheduleHint p) rest d hdc
      (by rw [hdi];exact hbin) bounds.parserBits (by have := bounds.large;omega) bounds.parserCounts hdempty)
    fun e ⟨⟨_,hep,_,_,_,_,hesh,hec,hefr⟩,herc,_,_⟩ => ?_
  have hek : e.env StageCertTests.scheduleCallKindVar=kindTag c.kind := by rw [hefr _ (by decide),hdk]
  refine Hs.seq (StageCertTests.loadAllScheduleFields_spec C e p hep (by omega) hec)
    fun f ⟨hfields,_,hfrest,hfc,hffr⟩ => ?_
  have hfk : f.env StageCertTests.scheduleCallKindVar=kindTag c.kind := by rw [hffr _ (by decide),hek]
  have hfit : 1+StageCertTests.callCircuitCount c.kind*(128*(p.J+1))<2^C.Wd := by
    rw [←StageCertTests.certificateMetadata_length]
    exact hcounter.2
  refine Hs.seq (setTestCensus_spec C f hfc c.kind p.J hfk (hfields .chainLength) hfit)
    fun g ⟨hgn,hgs,hgc,_⟩ => ?_
  have hgT : g.env testCountVar=(StageCertTests.certificateMetadata p c.kind).length := by
    rw [StageCertTests.certificateMetadata_length]
    exact hgn
  have hemit := StageRecovery.emitVariable_spec C g hgc testCountVar (by decide) bounds.width
    (by rw [hgT];omega)
  rw [hgT] at hemit
  refine hemit.mono le_rfl ?_
  rintro h ⟨hho,_,_,_⟩
  have hsame := Same.of_sh hgs
  have hfo : f.out=e.out := congrArg (fun q => q.2.1) hfrest
  have heo : e.out=d.out := congrArg Prod.fst hesh
  have hdo : d.out=b.out := congrArg (fun q => q.2.1) hdrest
  have hbo : b.out=a.out := congrArg Prod.fst hbs
  rw [hho,hsame.out,hfo,heo,hdo,hbo]

end NearQuarticWires.StageCertificateControl
