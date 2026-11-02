import Proof.Quartic.StageLift.PatternSource
import Proof.Quartic.StageCertTests.MemoryCallKind

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces

/-- Step 3, `sec:algorithm`, paper/paper.tex: retain the actual
call-kind tag before the amplifier initializes its ordinal register. -/
def retainPrintKind : St VV MM :=
  .seq StageCertTests.readRetainedCallKind
    (.op (.copy callKindVar StageCertTests.scheduleCallKindVar))

/-- Step 3, `sec:algorithm`, paper/paper.tex: the kind is physically
read from the finite original call, then retained outside all source-body
and amplifier scratch. This program precedes amplifier ordinal setup. -/
theorem retainPrintKind_spec (C : Ctx) (c : Call) (a : DS VV MM) (hc : Cst a)
    (hcall : a.ram callStore = (callWord c).map Bool.toNat)
    (hn : natBitLength c.n + 2 ≤ C.Wd)
    (hk : natBitLength (kindTag c.kind) + 2 ≤ C.Wd) :
    Hs C retainPrintKind a
      (a.rc callStore + 30 * natBitLength c.n + 30 * natBitLength (kindTag c.kind) + 69)
      (fun b => b.env callKindVar = kindTag c.kind ∧
        memorySourceRest callStore b = memorySourceRest callStore a ∧
        Cst b ∧ Fr a b (callKindVar :: StageRecovery.widthVar ::
          StageCertTests.scheduleCallKindVar :: rdNatT)) := by
  unfold retainPrintKind
  refine Hs.seq (t2 := 1) (StageCertTests.readRetainedCallKind_spec C a c hc hcall hn hk)
    fun b ⟨hbk, hbrest, _hbcursor, hbc, hbf⟩ => ?_
  refine (hs_copy C callKindVar StageCertTests.scheduleCallKindVar b (by decide)).mono le_rfl ?_
  rintro d rfl
  have hf : Fr a (b.set callKindVar (b.env StageCertTests.scheduleCallKindVar))
      (callKindVar :: StageRecovery.widthVar :: StageCertTests.scheduleCallKindVar :: rdNatT) :=
    (hbf.weaken (by
      intro x hx
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hx ⊢
      tauto)).trans (Fr.set _ _ (by simp))
  exact ⟨hbk, hbrest, Cst.of_fr hc hf (by decide), hf⟩

/-- Step 3 and `lem:residue`, paper/paper.tex: the actual call tag and circuit ordinal determine
exactly the original active circuit set. -/
theorem activeCircuit_from_kind (c : Call) (j : Fin 2) :
    j ∈ Builder.circuitSet c ↔ j.val = 0 ∨ kindTag c.kind = 1 := by
  cases hk : c.kind <;> fin_cases j <;> simp [Builder.circuitSet, hk, kindTag]

end NearQuarticWires.StageLift
