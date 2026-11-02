import Proof.Quartic.StageCertTests.CircuitLimit
import Proof.Quartic.StageLift.CallSource
import Proof.Quartic.StageLift.MemoryVariable

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertTests

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open StageRecovery (widthVar)

/-- `sec:algorithm`, paper/paper.tex:
the exact call kind is recovered by two actual natural-field
reads from the retained original call after a paid head return. -/
def readRetainedCallKind : St VV MM :=
  .seq (.op (.rwM StageLift.callStore))
    (.seq (StageLift.readMemoryVariable StageLift.callStore widthVar)
      (StageLift.readMemoryVariable StageLift.callStore scheduleCallKindVar))

/-- `sec:algorithm` and `prop:time`, paper/paper.tex: the kind is decoded from original raw
call bits, preserving every parameter, source and record word. -/
theorem readRetainedCallKind_spec (C : Ctx) (a : DS VV MM) (c : Call) (hc : Cst a)
    (hcall : a.ram StageLift.callStore = (callWord c).map Bool.toNat)
    (hn : natBitLength c.n+2 ≤ C.Wd) (hk : natBitLength (kindTag c.kind)+2 ≤ C.Wd) :
    Hs C readRetainedCallKind a
      (a.rc StageLift.callStore+30*natBitLength c.n+30*natBitLength (kindTag c.kind)+67)
      (fun b => b.env scheduleCallKindVar = kindTag c.kind ∧
        StageLift.memorySourceRest StageLift.callStore b = StageLift.memorySourceRest StageLift.callStore a ∧
        b.rc StageLift.callStore = (natWord c.n).length+(natWord (kindTag c.kind)).length ∧
        Cst b ∧ Fr a b ([widthVar,scheduleCallKindVar] ++ rdNatT)) := by
  unfold readRetainedCallKind
  refine (Hs.seq (t2 := 30*natBitLength c.n+30*natBitLength (kindTag c.kind)+65)
    (hs_rwM C StageLift.callStore a) fun b hb => ?_).mono (by omega) (fun _ h => h)
  subst b
  have hinput : (callWord c).drop ((a.rew StageLift.callStore).rc StageLift.callStore) =
      natWord c.n ++ (natWord (kindTag c.kind) ++ circuitWord c.first ++ circuitWord c.second ++
        listWord natWord c.parity ++ ratWord c.radius) := by
    simp only [DS.rew,Function.update_self,List.drop_zero,callWord,List.append_assoc]
  refine (Hs.seq (t2 := 30*natBitLength (kindTag c.kind)+32)
    (StageLift.readMemoryVariable_spec C StageLift.callStore (callWord c) (a.rew StageLift.callStore)
      ⟨hc.z,hc.one,hc.two⟩ hcall widthVar (by decide) (by decide) c.n _ hinput hn)
    fun b ⟨_,hbrc,hbrest,hbc,hbfr⟩ => ?_).mono (by omega) (fun _ h => h)
  have hbram : b.ram = a.ram := congrArg (fun q => q.2.2.1) hbrest
  have hbcursor : b.rc StageLift.callStore = (natWord c.n).length := by simpa [DS.rew] using hbrc
  have hbin : (callWord c).drop (b.rc StageLift.callStore) = natWord (kindTag c.kind) ++
      (circuitWord c.first ++ circuitWord c.second ++ listWord natWord c.parity ++ ratWord c.radius) := by
    rw [hbcursor]
    simp only [callWord,List.append_assoc,List.drop_left]
  refine (StageLift.readMemoryVariable_spec C StageLift.callStore (callWord c) b hbc
    (by rw [hbram];exact hcall) scheduleCallKindVar (by decide) (by decide)
    (kindTag c.kind) _ hbin hk).mono le_rfl ?_
  rintro d ⟨hdv,hdrc,hdrest,hdc,hdfr⟩
  refine ⟨hdv,?_,by rw [hdrc,hbcursor],hdc,
    Fr.trans (Fr.weaken hbfr (by intro x hx;simp only [List.mem_append,List.mem_cons] at hx ⊢;tauto))
      (Fr.weaken hdfr (by intro x hx;simp only [List.mem_append,List.mem_cons] at hx ⊢;tauto))⟩
  exact hdrest.trans (by simpa [StageLift.memorySourceRest,DS.rew,Function.update_idem] using hbrest)

end NearQuarticWires.StageCertTests
