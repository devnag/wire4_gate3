import Proof.Quartic.StagePrintTuple.TermStageRun
import Proof.Quartic.StagePrintTuple.TermStageSpan
import Proof.Quartic.StagePrintTuple.TermStagePriceContract
import Proof.Quartic.StageNativeKids.Machine

set_option autoImplicit false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms

/-- `lem:print` and `prop:time`, paper/paper.tex: the complete original-source monomial implementation
binds the genuine native printer and its same proved budget. The only
remaining constructor argument is the exact individual clock theorem,
which its public constant supplies from the proved actual cost bound. -/
noncomputable def termStageMachineOfBound (hprice : TermStageCostBound) :
    TermStageMachine StageNativeKids.nativeKidsWordFunction StageNativeKids.nativeStagePrice := by
  let native := StageNativeKids.nativeKidsWordFunction
  let span := termStageSpan native.program
  let hn := termStageSpan_native native.program
  let hc := termStageSpan_coefficient native.program
  let hs := termStageSpan_support native.program
  let ht := termStageSpan_tuple native.program
  let hstack := termStageSpan_stack native.program
  let capacity (r : TermCutRequest) := 1+(List.ofFn fun j : Fin r.terms.length=>
    termStageCapacity StageNativeKids.NativeKidsRequest.budget r j.val j.isLt).sum
  let cost (r : TermCutRequest) (k : ℕ) := if hk:k<r.terms.length then
    termStageCost StageNativeKids.NativeKidsRequest.budget r k hk else 0
  refine ⟨span,termStageProgram native span hn hc hs ht hstack,capacity,cost,?_,?_⟩
  · intro r k hk cap hcap
    have hm : termStageCapacity StageNativeKids.NativeKidsRequest.budget r k hk∈
        List.ofFn (fun j : Fin r.terms.length=>
          termStageCapacity StageNativeKids.NativeKidsRequest.budget r j.val j.isLt) :=
      List.mem_ofFn.mpr ⟨⟨k,hk⟩,rfl⟩
    have hsum := List.le_sum_of_mem hm
    have hstep : termStageCapacity StageNativeKids.NativeKidsRequest.budget r k hk ≤ cap :=
      hsum.trans ((Nat.le_add_left _ _).trans hcap)
    obtain ⟨τ,et,ht'⟩ := termStageRun native span hn hc hs ht hstack r k hk cap hstep
    exact ⟨τ,by simpa only [cost,dif_pos hk] using et,ht'⟩
  · obtain ⟨C,E,hC,hE,hp⟩ := hprice
    refine ⟨C,E,hC,hE,?_⟩
    intro r mc hmc hk k hvalid
    simpa only [cost,dif_pos hvalid] using hp r mc hmc hk k hvalid

end NearQuarticWires.StageTuple
