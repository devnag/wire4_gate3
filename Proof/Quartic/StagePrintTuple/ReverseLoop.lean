import Proof.Quartic.StagePrintTuple.ReverseBody
import Proof.Quartic.Control.Loop

set_option autoImplicit false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP
open NearQuarticWires.Control

/-- `prop:time`, paper/paper.tex: the complete
reverse loop has an analysis capacity covering its actual count and
each actual finite iteration, without a capacity-sized runtime sweep. -/
def reverseLoopCapacity (B : StageNativeKids.NativeKidsRequest→ℕ)
    (r : TermCutRequest)
    (data : MonomialData (17*(Builder.allGates r.header.call).length)) : ℕ :=
  data.order.length+1+(List.ofFn fun j : Fin data.order.length=>
    reverseStepCapacity B r data j.val j.isLt).sum

/-- `prop:time`, paper/paper.tex: every support
iteration pays its genuine finite stage bound and loop transitions.
The extra support-length factor is polynomial in the monomial degree. -/
def reverseLoopCost (B : StageNativeKids.NativeKidsRequest→ℕ)
    (r : TermCutRequest)
    (data : MonomialData (17*(Builder.allGates r.header.call).length)) : ℕ :=
  data.order.length*((List.ofFn fun j : Fin data.order.length=>
    reverseStepCost B r data j.val j.isLt).sum+4)+1

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual reverse counter loop reaches the full
original-child Cartesian product in the specified lexicographic order,
including empty supports and zero-child intermediate pools. -/
theorem reverseLoop_run {B : StageNativeKids.NativeKidsRequest→ℕ}
    (native : WordFunction StageNativeKids.NativeKidsRequest StageNativeKids.NativeKidsRequest.word
      StageNativeKids.NativeKidsRequest.output B)
    (r : TermCutRequest)
    (data : MonomialData (17*(Builder.allGates r.header.call).length))
    (span cap : ℕ) (hn : native.program.tapeCount ≤ span)
    (hs : supportIndexWordFunction.program.tapeCount ≤ span)
    (ht : tupleRecordPrinter.program.tapeCount ≤ span)
    (hcap : reverseLoopCapacity B r data ≤ cap)
    (σ : WState (span+29) 32) (hσ : SimW (data.reverseState r span 0) σ) :
    ∃τ,WXExec cap
      (kernelReverseLoop StageTupleNativePhase.nativePhaseProgram native span hn hs ht)
      σ τ (reverseLoopCost B r data) ∧
        SimW (data.reverseState r span data.order.length) τ := by
  let stepBound := (List.ofFn fun j : Fin data.order.length=>
    reverseStepCost B r data j.val j.isLt).sum
  have hcount : data.order.length ≤ cap := by unfold reverseLoopCapacity at hcap;omega
  have e := Runs.count (cap:=cap) (K:=15)
    (body:=kernelReverseBody StageTupleNativePhase.nativePhaseProgram native span hn hs ht)
    stepBound data.order.length (fun k τ=>SimW (data.reverseState r span k) τ) hcount
    (by
      intro k hk a ha _
      have hkc : reverseStepCapacity B r data k hk ≤ cap := by
        have hm := List.le_sum_of_mem (show reverseStepCapacity B r data k hk ∈
          List.ofFn (fun j : Fin data.order.length=>reverseStepCapacity B r data j.val j.isLt) from
            List.mem_ofFn.mpr ⟨⟨k,hk⟩,rfl⟩)
        unfold reverseLoopCapacity at hcap
        omega
      have hks : reverseStepCost B r data k hk ≤ stepBound :=
        List.le_sum_of_mem (List.mem_ofFn.mpr ⟨⟨k,hk⟩,rfl⟩)
      obtain ⟨b,eb,hb⟩ := reverseBody_run native r data span k cap hk hn hs ht hkc
      have hsub : data.order.length-k-1=data.order.length-(k+1) := by omega
      have hsim := simW_setv ha 15 (data.order.length-(k+1))
      obtain ⟨c,ec,hc⟩ := wxexec_sim eb (a.setv 15 (data.order.length-k-1))
        (by simpa only [hsub] using hsim)
      have hfinal := SimW.trans hb hc
      refine ⟨c,ec.mono hks,hfinal,?_⟩
      rw [hfinal.val,data.reverseState_index]
      omega)
    σ hσ (by rw [hσ.val,data.reverseState_index];omega)
  obtain ⟨τ,et,hτ,_⟩ := e
  exact ⟨τ,et,hτ⟩

end NearQuarticWires.StageTuple
