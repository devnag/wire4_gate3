import Proof.Quartic.StagePrintTuple.Calls
import Proof.Quartic.Control.Round

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.WorkerArith (inTape)
open NearQuarticWires.Control

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: a reusable
callee bank is genuinely blank before the next finite request is
formatted on its input tape. -/
structure CallBlank (p : Program) (s : Site p ns nr) (σ : WState ns nr) : Prop where
  bank : ∀j,σ.st (s.bank j)=[]
  heads : ∀j,σ.sh (s.bank j)=0
  tally : σ.st s.tally=[]
  tallyHead : σ.sh s.tally=0
  guard : σ.st s.guard=[]
  guardHead : σ.sh s.guard=0
  ruler : Worker.Blank (σ.st s.ruler)
  rulerHead : σ.sh s.ruler=0
  registers : ∀i,σ.val (s.regs i)=0

/-- `lem:print`, paper/paper.tex: physically
formatting the exact finite input on a genuinely blank call bank
establishes every cold-callee start condition. -/
theorem CallBlank.ready {p : Program} {s : Site p ns nr} {σ : WState ns nr}
    (h : CallBlank p s σ) (word : List Bool) :
    CallReady p s word (σ.sets s.input (frame word)) := by
  refine ⟨?_,h.heads,?_,h.tallyHead,?_,h.guardHead,?_,h.rulerHead,h.registers⟩
  · intro j
    change Function.update σ.st s.input (frame word) (s.bank j)=
      (if j.val=0 then frame word else [])
    by_cases hj:j.val=0
    · have hj' : j=inTape p := Fin.ext hj
      subst j
      simp [Site.input,inTape]
    · have hb : s.bank j≠s.input := by
        intro he
        have hh:=s.bank_inj he
        apply hj
        rw [hh]
        rfl
      simp only [Function.update_of_ne hb,h.bank,if_neg hj]
  · simpa only [WState.sets_st,Site.input,Function.update_of_ne (s.tally_ne (inTape p)).symm] using h.tally
  · simpa only [WState.sets_st,Site.input,Function.update_of_ne (s.guard_ne (inTape p)).symm] using h.guard
  · simpa only [WState.sets_st,Site.input,Function.update_of_ne (s.ruler_ne (inTape p)).symm] using h.ruler

/-- `lem:print`, paper/paper.tex: advancing an
exterior tuple-history cursor preserves the complete blank call bank. -/
theorem CallBlank.seth {p : Program} {s : Site p ns nr} {σ : WState ns nr}
    (h : CallBlank p s σ) (src : Fin (ns+1)) (k : ℕ)
    (hout : s.Out src) (hr : src≠s.ruler) : CallBlank p s (σ.seth src k) := by
  refine ⟨h.bank,?_,h.tally,?_,h.guard,?_,h.ruler,?_,h.registers⟩
  · intro j
    simpa only [WState.seth_sh,Function.update_of_ne (hout.1 j)] using h.heads j
  · simpa only [WState.seth_sh,Function.update_of_ne hout.2.1.symm] using h.tallyHead
  · simpa only [WState.seth_sh,Function.update_of_ne hout.2.2.symm] using h.guardHead
  · simpa only [WState.seth_sh,Function.update_of_ne hr.symm] using h.rulerHead

/-- `lem:print`, paper/paper.tex: cleaning an
already blank work bank preserves the complete exterior state. -/
theorem CallBlank.clean {p : Program} {s : Site p ns nr} {σ : WState ns nr}
    (h : CallBlank p s σ) : cleanState s σ=σ :=
  StagePrint.cleanState_self s σ h.bank h.heads h.tally h.guard

end NearQuarticWires.StageTuple
