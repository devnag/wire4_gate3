import Proof.Quartic.StageNativeKidsPool.ColdSource
import Proof.Gates.Codec.Unframe

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageNativeKidsPool
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close NearCubicGates.Close.Codec NearCubicGates.Close.WordPrograms

variable {Q R : Type} {input : R→List Bool}

/-- `lem:print`, paper/paper.tex: the
actual original compiler/counter has one private ordinary blank ruler. -/
def counterRuler (counter row : Program) : Fin (streams counter row+1):=
  ⟨16,by unfold streams;omega⟩

/-- `lem:print`, paper/paper.tex: the
retained original source is copied once into the real counter bank;
no child count, cache or selected row is supplied to that computation. -/
def counterCopyProgram (counter row : Program) : WM (streams counter row) 16:=
  copyRW ⟨2,by unfold streams;omega⟩ (counterMap counter row (WorkerArith.inTape counter)) 0 1 2

/-- `prop:time`, paper/paper.tex: the
source copy into the actual counter bank has a linear finite byte clock. -/
def counterCopyCost (source : List Bool) : ℕ:=200*(source.length+1)

/-- `lem:print`, paper/paper.tex: actual
loaded indexed original bytes are copied into the cold original counter,
retaining the source and resetting both physical tape heads. -/
theorem counterCopy_spec (F : Q→Family R input) (width countBudget : Q→ℕ)
    (counter row : Program) (q : Q) (cap : ℕ)
    (hcap : 4*(F q).source.length+4≤cap) :
    WExec cap (counterCopyProgram counter row) (loaded F width countBudget counter row q)
      ((loaded F width countBudget counter row q).sets
        (counterMap counter row (WorkerArith.inTape counter)) (frame (F q).source))
      (counterCopyCost (F q).source) := by
  let σ:=loaded F width countBudget counter row q
  have hsd : (⟨2,by unfold streams;omega⟩ : Fin (streams counter row+1))≠
      counterMap counter row (WorkerArith.inTape counter):=by
    intro h;have hv:=congrArg Fin.val h;change 2=20+_ at hv;omega
  have hc : ¬(20+(WorkerArith.inTape counter).val)<13:=by omega
  have h13 : 20+(WorkerArith.inTape counter).val≠13:=by omega
  have h16 : 20+(WorkerArith.inTape counter).val≠16:=by omega
  have e:=copyRW_spec cap ⟨2,by unfold streams;omega⟩
    (counterMap counter row (WorkerArith.inTape counter)) hsd
    (0 : Fin 16) 1 2 (by decide) (by decide) (by decide) (F q).source [] σ
    (by simp [σ,loaded,fields]) rfl
    (by simp [σ,loaded,counterMap,hc,lens,h13,h16]) rfl rfl rfl rfl hcap
  exact e.mono (by unfold counterCopyCost;omega)

/-- `lem:print`, paper/paper.tex: the
only count-producing call is the real original source compiler and
record counter, run once after its physically constructed source copy. -/
noncomputable def counterProgram (counter row : Program) : WMX (streams counter row) 16:=
  .seq (.wm (counterCopyProgram counter row))
    (.machZ counter.machine (counterMap counter row) (counterRuler counter row))

/-- `lem:print` and `prop:time`, paper/paper.tex: the complete actual source-selected count
call returns the exact finite count codec and a reset ordinary bank,
while preserving all retained source and row-bank tapes. -/
theorem counterProgram_spec (F : Q→Family R input) (width countBudget : Q→ℕ)
    (f : WordFunction Q (fun q=>(F q).source)
      (fun q=>frame (natWord (F q).count)) countBudget)
    (row : Program) (q : Q) (cap : ℕ) (hcap : 4*(F q).source.length+4≤cap) :
    ∃τ tout,
      WXExec cap (counterProgram f.program row) (loaded F width countBudget f.program row q) τ
        (counterCopyCost (F q).source+2*countBudget q+3) ∧
      Docked (counterMap f.program row)
        ((loaded F width countBudget f.program row q).sets
          (counterMap f.program row (WorkerArith.inTape f.program)) (frame (F q).source))
        τ (fun _=>0) tout ∧
      τ.st (counterMap f.program row f.program.outputTape)=frame (natWord (F q).count) := by
  let σ:=loaded F width countBudget f.program row q
  let d:=σ.sets (counterMap f.program row (WorkerArith.inTape f.program)) (frame (F q).source)
  have ec:=counterCopy_spec F width countBudget f.program row q cap hcap
  have hi : Function.Injective (counterMap f.program row):=by
    intro i j h;apply Fin.ext;have hv:=congrArg Fin.val h;simp only [counterMap,Fin.val_mk] at hv;omega
  have hbr : ∀j,counterMap f.program row j≠counterRuler f.program row:=by
    intro j h;have hv:=congrArg Fin.val h;change 20+j.val=16 at hv;omega
  have hin : ∀j,d.st (counterMap f.program row j)=f.program.inputTapes (F q).source j:=by
    intro j
    by_cases hj:j=WorkerArith.inTape f.program
    · subst hj;simp [d,σ,Program.inputTapes,WorkerArith.inTape]
    · have hn : counterMap f.program row j≠counterMap f.program row (WorkerArith.inTape f.program):=hi.ne hj
      have hj0 : j.val≠0:=by intro h;exact hj ((WorkerArith.inTape_iff f.program j).2 h)
      have h13 : 20+j.val≠13:=by omega
      have h16 : 20+j.val≠16:=by omega
      simp only [d,WState.sets_st,Function.update_of_ne hn]
      simp [σ,loaded,counterMap,show ¬20+j.val<13 by omega,lens,h13,h16,
        Program.inputTapes,hj0]
  have hpad : d.st (counterRuler f.program row)=List.replicate (countBudget q) false:=by
    simp only [d,WState.sets_st,Function.update_of_ne (hbr (WorkerArith.inTape f.program)).symm]
    rfl
  obtain ⟨actual,hr,ho⟩:=f.realizes q
  have hinEq : (fun j=>d.st (counterMap f.program row j))=f.program.inputTapes (F q).source:=funext hin
  rw [←hinEq] at hr
  obtain ⟨τ,er,hd⟩:=WXExec.machZ_run (cap:=cap) hi hbr d hr (fun _=>rfl) hpad rfl le_rfl
  exact ⟨τ,actual.final.tapes,(WXExec.seq (WXExec.wm ec) er).mono (by omega),hd,by rw [hd.st,ho]⟩

end NearQuarticWires.StageNativeKidsPool
