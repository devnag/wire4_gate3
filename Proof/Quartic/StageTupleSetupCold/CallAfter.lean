import Proof.Quartic.StageTupleSetupCold.Helpers

set_option autoImplicit false

namespace NearQuarticWires.StageTupleSetupCold

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms

/-- `lem:print`, paper/paper.tex: a
private one-shot bank with reset heads preserves global zero heads
when every tape outside that bank is retained unchanged. -/
theorem docked_zero_heads {ns nr t : ℕ} {bank : Fin t→Fin (ns+1)}
    {σ τ : WState ns nr} {out : Fin t→List Bool}
    (hd : Docked bank σ τ (fun _=>0) out) (hz : ∀i,σ.sh i=0) : ∀i,τ.sh i=0 := by
  intro i
  by_cases hi : ∃j,bank j=i
  · obtain ⟨j,rfl⟩:=hi
    exact hd.sh j
  · exact ((hd.other i (fun j h=>hi ⟨j,h⟩)).2).trans (hz i)

/-- `lem:print` and `prop:time`, paper/paper.tex: the physical small-packet framer
and actual ordinary helper execute on one private cold bank. The
entire stage preserves every external source and controller register,
and returns the helper's genuine output with reset bank heads. -/
theorem call_after_input {ns nr : ℕ} {Request : Type}
    {input output : Request→List Bool} {budget : Request→ℕ}
    (f : WordFunction Request input output budget) (req : Request)
    (cap : ℕ) (bank : Fin f.program.tapeCount→Fin (ns+1)) (hb : Function.Injective bank)
    (zero : Fin f.program.tapeCount) (hzero : zero.val=0)
    (ruler : Fin (ns+1)) (hbr : ∀j,bank j≠ruler)
    (inputProgram : WM ns nr) (inputCost : ℕ) (σ : WState ns nr)
    (he : WExec cap inputProgram σ (σ.sets (bank zero) (frame (input req))) inputCost)
    (hcold : ∀j,σ.st (bank j)=[]) (hh : ∀j,σ.sh (bank j)=0)
    (hpad : σ.st ruler=List.replicate (budget req) false) (hrh : σ.sh ruler=0) :
    ∃τ tout,WXExec cap (.seq (.wm inputProgram) (.machZ f.program.machine bank ruler)) σ τ
      (inputCost+1+(2*budget req+2)) ∧
      Docked bank σ τ (fun _=>0) tout ∧
      τ.st (bank f.program.outputTape)=output req := by
  have hin : ∀j,(σ.sets (bank zero) (frame (input req))).st (bank j)=
      f.program.inputTapes (input req) j := by
    intro j
    by_cases hj : j.val=0
    · have hje : j=zero:=Fin.ext (hj.trans hzero.symm)
      subst j
      simp only [WState.sets_st,Function.update_self,Program.inputTapes,hzero,ite_true]
    · have hne : bank j≠bank zero := by
        intro h
        have hv:=congrArg Fin.val (hb h)
        exact hj (hv.trans hzero)
      simp only [WState.sets_st,Function.update_of_ne hne,Program.inputTapes,if_neg hj,hcold]
  have hpad' : (σ.sets (bank zero) (frame (input req))).st ruler=
      List.replicate (budget req) false := by
    simpa only [WState.sets_st,Function.update_of_ne (hbr zero).symm] using hpad
  obtain ⟨τ,tout,hcall,hd,ho⟩:=StageTupleSetup.OneShotCore.run f req cap bank hb ruler hbr
    (σ.sets (bank zero) (frame (input req))) hin hh hpad' hrh
  refine ⟨τ,tout,(WXExec.wm he).seq hcall,⟨hd.st,hd.sh,?_,hd.val,hd.cell⟩,ho⟩
  intro i hi
  have h:=hd.other i hi
  simpa only [WState.sets_st,Function.update_of_ne (hi zero).symm,WState.sets_sh] using h

end NearQuarticWires.StageTupleSetupCold
