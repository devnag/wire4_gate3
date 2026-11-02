import Proof.Quartic.StageGreedyContext.ArityPrefix
import Proof.Gates.CounterMachine.TabCallDock
import Proof.Gates.Expand.PolyTabPack

/-!
# One private physical context bank and a once-read carrier

Paper: `lem:print`, paper/paper.tex,
and `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyContext

open NearCubicWires NearCubicWires.RepairOrdinary

/-- `lem:print`, paper/paper.tex: the
single common-context call has its own physical tape bank. -/
def bank (p : Program) (j : Fin p.tapeCount) : Fin (p.tapeCount+4) :=
  ⟨4+j.val,by omega⟩

/-- `lem:print`, paper/paper.tex: the
context bank has no aliased physical tapes. -/
theorem bank_injective (p : Program) : Function.Injective (bank p) := by
  intro i j h
  apply Fin.ext
  have hh:=congrArg Fin.val h
  simp only [bank,Fin.val_mk] at hh
  omega

/-- `prop:time`, paper/paper.tex: one
separate reset ruler serves the sole common-context call. -/
def ruler (p : Program) : Fin (p.tapeCount+4) := ⟨3,by omega⟩

/-- `lem:print`, paper/paper.tex: the
context call's reset ruler is outside all of its actual tapes. -/
theorem bank_ne_ruler (p : Program) (j : Fin p.tapeCount) : bank p j≠ruler p := by
  intro h
  have hh:=congrArg Fin.val h
  change 4+j.val=3 at hh
  omega

/-- `lem:print`, paper/paper.tex: the
original carrier, context frame and final stream remain outside the
single physical context-call bank. -/
theorem bank_off (p : Program) (j : Fin p.tapeCount) :
    bank p j≠(0 : Fin (p.tapeCount+4)) ∧ bank p j≠1 ∧ bank p j≠2 := by
  constructor
  · intro h;have hh:=congrArg Fin.val h;change 4+j.val=0 at hh;omega
  · constructor
    · intro h;have hh:=congrArg Fin.val h;change 4+j.val=1 at hh;omega
    · intro h;have hh:=congrArg Fin.val h;change 4+j.val=2 at hh;omega

/-- `prop:time`, paper/paper.tex: the
finite prefix registers occupy fixed distinct scalar slots. -/
def registers : Fin 16 ↪ Fin 24 where
  toFun j:=⟨j.val+4,by have:=j.isLt;omega⟩
  inj':=by
    intro i j h
    apply Fin.ext
    have hh:=congrArg Fin.val h
    change i.val+4=j.val+4 at hh
    omega

end NearQuarticWires.StageGreedyContext
