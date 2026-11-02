import Proof.Quartic.StagePrintTuple.CacheErase

set_option autoImplicit false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close.WordPrograms

variable {ns nr : ℕ}

/-- `lem:print` and `prop:time`, paper/paper.tex: erasing a finite reply with its measured copy count
produces a reusable blank cache, zero head and zero length counter.
Only the real finite reply prefix is touched. -/
theorem eraseMeasuredCache_spec (cap : ℕ) (src : Fin (ns+1)) (SC : Fin nr)
    (bits : List Bool) (σ : WState ns nr) (hs : σ.st src=bits)
    (hh : σ.sh src=bits.length) (hc : σ.val SC=bits.length)
    (hcap : bits.length ≤ cap) :
    ∃τ,WExec cap (eraseCacheBackward src SC) σ τ (10*bits.length+1) ∧
      SimW (((σ.sets src []).seth src 0).setv SC 0) τ := by
  have e := eraseCacheBackward_spec cap src SC bits [] σ
    (by simpa using hs) hh hc hcap
  refine ⟨_,e,?_⟩
  refine ⟨rfl,rfl,rfl,?_⟩
  intro i
  by_cases hi:i=src
  · subst i
    simpa only [WState.setv_st,WState.seth_st,WState.sets_st,Function.update_self,
      List.append_nil] using
      (rdEq_blank (List.replicate bits.length false) (by simp)).symm
  · simp only [WState.setv_st,WState.seth_st,WState.sets_st,Function.update_of_ne hi]
    exact RdEq.refl _

end NearQuarticWires.StageTuple
