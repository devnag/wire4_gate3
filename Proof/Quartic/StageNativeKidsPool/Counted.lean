import Proof.Quartic.StageNativeKidsPool.CounterCall

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageNativeKidsPool
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close NearCubicGates.Close.WordPrograms

variable {Q R : Type} {input : R→List Bool}

/-- `lem:print`, paper/paper.tex: after
one real original-source counter call, its exact result codec and all
retained source and future row-bank states are physically available. -/
structure Counted (F : Q→Family R input) (width countBudget : Q→ℕ)
    (counter row : Program) (q : Q) (σ : WState (streams counter row) 16) : Prop where
  count : σ.st (counterMap counter row counter.outputTape)=frame (natWord (F q).count)
  count_head : σ.sh (counterMap counter row counter.outputTape)=0
  small : ∀i : Fin (streams counter row+1),i.val<20→
    σ.st i=(loaded F width countBudget counter row q).st i ∧ σ.sh i=0
  row_bank : ∀j,σ.st (rowMap counter row j)=[] ∧ σ.sh (rowMap counter row j)=0
  registers : ∀i,σ.val i=0

/-- `lem:print`, paper/paper.tex: every
actual counter tape lies outside all finite loaded source fields and
all small output and call-ruler streams. -/
theorem counterMap_not_small (counter row : Program) (j : Fin counter.tapeCount)
    (i : Fin (streams counter row+1)) (hi : i.val<20) : counterMap counter row j≠i := by
  intro h;have hv:=congrArg Fin.val h;change 20+j.val=i.val at hv;omega

/-- `lem:print`, paper/paper.tex: the
real original counter and original-row banks have disjoint tape ranges. -/
theorem counterMap_ne_rowMap (counter row : Program) (i : Fin counter.tapeCount)
    (j : Fin row.tapeCount) : counterMap counter row i≠rowMap counter row j := by
  intro h;have hv:=congrArg Fin.val h;have:=i.isLt
  simp only [counterMap,rowMap,Fin.val_mk] at hv
  omega

/-- `lem:print` and `prop:time`, paper/paper.tex: the one actual original-source count
computation establishes all inputs needed by the generated row loop,
without supplying any count, selected row or native pool as input. -/
theorem counted_exec (F : Q→Family R input) (width countBudget : Q→ℕ)
    (f : WordFunction Q (fun q=>(F q).source)
      (fun q=>frame (natWord (F q).count)) countBudget)
    (row : Program) (q : Q) (cap : ℕ) (hcap : 4*(F q).source.length+4≤cap) :
    ∃τ,WXExec cap (counterProgram f.program row) (loaded F width countBudget f.program row q) τ
      (counterCopyCost (F q).source+2*countBudget q+3) ∧
      Counted F width countBudget f.program row q τ := by
  obtain ⟨τ,tout,he,hd,ho⟩:=counterProgram_spec F width countBudget f row q cap hcap
  refine ⟨τ,he,ho,hd.sh _,?_,?_,?_⟩
  · intro i hi
    obtain ⟨hst,hsh⟩:=hd.other i (fun j=>counterMap_not_small _ _ j i hi)
    constructor
    · simpa only [WState.sets_st,Function.update_of_ne
        (counterMap_not_small _ _ (WorkerArith.inTape f.program) i hi).symm] using hst
    · exact hsh
  · intro j
    obtain ⟨hst,hsh⟩:=hd.other (rowMap f.program row j)
      (fun i=>counterMap_ne_rowMap _ _ i j)
    constructor
    · rw [hst]
      simp only [WState.sets_st,Function.update_of_ne
        (counterMap_ne_rowMap _ _ (WorkerArith.inTape f.program) j).symm]
      simp [loaded,rowMap,lens,show ¬20+f.program.tapeCount+j.val<13 by omega,
        show 20+f.program.tapeCount+j.val≠13 by omega,
        show 20+f.program.tapeCount+j.val≠16 by omega]
    · exact hsh
  · intro i
    rw [hd.val]
    rfl

end NearQuarticWires.StageNativeKidsPool
