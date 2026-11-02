import Proof.Quartic.StagePrintTuple.CallInput

set_option autoImplicit false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearQuarticWires.Control

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: replacing a
finite exterior cache preserves the genuinely blank reusable callee
bank and its physical call controls. -/
theorem CallBlank.sets {p : Program} {s : Site p ns nr} {σ : WState ns nr}
    (h : CallBlank p s σ) (src : Fin (ns+1)) (bits : List Bool)
    (hout : s.Out src) (hr : src≠s.ruler) : CallBlank p s (σ.sets src bits) := by
  refine ⟨?_,h.heads,?_,h.tallyHead,?_,h.guardHead,?_,h.rulerHead,h.registers⟩
  · intro j
    simpa only [WState.sets_st,Function.update_of_ne (hout.1 j)] using h.bank j
  · simpa only [WState.sets_st,Function.update_of_ne hout.2.1.symm] using h.tally
  · simpa only [WState.sets_st,Function.update_of_ne hout.2.2.symm] using h.guard
  · simpa only [WState.sets_st,Function.update_of_ne hr.symm] using h.ruler

/-- `lem:print`, paper/paper.tex: a persistent
source or tuple counter is disjoint from every call scratch register,
so its actual update leaves the cold-call invariant intact. -/
theorem CallBlank.setv {p : Program} {s : Site p ns nr} {σ : WState ns nr}
    (h : CallBlank p s σ) (R : Fin nr) (value : ℕ)
    (hR : ∀i,s.regs i≠R) : CallBlank p s (σ.setv R value) := by
  refine ⟨h.bank,h.heads,h.tally,h.tallyHead,h.guard,h.guardHead,h.ruler,h.rulerHead,?_⟩
  intro i
  simpa only [WState.setv_val,Function.update_of_ne (hR i)] using h.registers i

end NearQuarticWires.StageTuple
