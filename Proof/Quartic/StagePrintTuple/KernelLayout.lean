import Proof.Quartic.StagePrintTuple.CoefficientMachine
import Proof.Quartic.StagePrintTuple.SupportIndexMachine
import Proof.Quartic.StagePrintTuple.RecordOutputs
import Proof.Quartic.Control.Round

set_option autoImplicit false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms
open NearQuarticWires.Control

/-- `lem:print`, paper/paper.tex: thirty fixed
exterior tapes hold the retained source, finite caches, tuple history,
cut output and call controls, before one shared genuine callee bank. -/
def kernelLocal (span : ℕ) : Fin 30↪Fin (span+30) :=
  ⟨fun i=>⟨i.val,by omega⟩,by
    intro i j h
    apply Fin.ext
    exact congrArg (fun x : Fin (span+30)=>x.val) h⟩

/-- `lem:print`, paper/paper.tex: all actual
callee machines reuse an initial portion of one fixed work bank. -/
def kernelBank (span : ℕ) (p : Program) (hp : p.tapeCount≤ span) :
    Fin p.tapeCount→Fin (span+30) := fun j=>⟨30+j.val,by omega⟩

/-- `lem:print`, paper/paper.tex: four physical
call scratch registers are separate from source-local arithmetic and
all persistent tuple, support, monomial and output counters. -/
def kernelCallRegisters : Fin 4↪Fin 32 := ⟨![20,21,22,23],by decide⟩

/-- `lem:print`, paper/paper.tex: one concrete
reusable call site fixes every callee tape, tally, guard, reset ruler and
scratch register; no allocator is a runtime input. -/
def kernelSite (span : ℕ) (p : Program) (hp : p.tapeCount≤ span) : Site p (span+29) 32 where
  bank := kernelBank span p hp
  tally := kernelLocal span 27
  guard := kernelLocal span 28
  ruler := kernelLocal span 29
  regs := kernelCallRegisters
  bank_inj := by
    intro i j h
    apply Fin.ext
    have hh:=congrArg Fin.val h
    simp only [kernelBank,Fin.val_mk] at hh
    omega
  tally_ne := by intro j h;have hh:=congrArg Fin.val h;change 30+j.val=27 at hh;omega
  guard_ne := by intro j h;have hh:=congrArg Fin.val h;change 30+j.val=28 at hh;omega
  ruler_ne := by intro j h;have hh:=congrArg Fin.val h;change 30+j.val=29 at hh;omega
  tally_guard := by intro h;have hh:=congrArg Fin.val h;change 27=28 at hh;omega
  tally_ruler := by intro h;have hh:=congrArg Fin.val h;change 27=29 at hh;omega
  guard_ruler := by intro h;have hh:=congrArg Fin.val h;change 28=29 at hh;omega

/-- `lem:print`, paper/paper.tex: every retained
source or output tape outside the three call-control slots is exterior
to every actual callee bank. -/
theorem kernelSite_out (span : ℕ) (p : Program) (hp : p.tapeCount≤ span)
    (i : Fin 30) (ht : i≠27) (hg : i≠28) :
    (kernelSite span p hp).Out (kernelLocal span i) := by
  refine ⟨?_,?_,?_⟩
  · intro j h
    have hh:=congrArg Fin.val h
    change 30+j.val=i.val at hh
    have hi:=i.isLt
    omega
  · exact (kernelLocal span).injective.ne ht
  · exact (kernelLocal span).injective.ne hg

/-- `lem:print`, paper/paper.tex: retained
source and cache tapes also avoid the actual shared reset ruler. -/
theorem kernelSite_ruler_ne (span : ℕ) (p : Program) (hp : p.tapeCount≤ span)
    (i : Fin 30) (hi : i≠29) : kernelLocal span i≠(kernelSite span p hp).ruler :=
  (kernelLocal span).injective.ne hi

/-- `lem:print`, paper/paper.tex: the complete
monomial formatter uses only its eleven source-local registers. -/
def kernelMonomialRegisters : Fin 11↪Fin 32 :=
  ⟨fun i=>⟨i.val,by omega⟩,by
    intro i j h
    apply Fin.ext
    exact congrArg (fun x : Fin 32=>x.val) h⟩

/-- `lem:print`, paper/paper.tex: actual
Cartesian formatting uses four scratch registers and the persistent
row-field, processed-stride, child-count and tuple-count registers. -/
def kernelCartesianRegisters : Fin 8↪Fin 32 := ⟨![0,1,2,3,11,12,13,14],by decide⟩

/-- `lem:print`, paper/paper.tex: actual tuple
count multiplication preserves the fixed row-field count and updates
only the processed stride and genuine current tuple count. -/
def kernelCounterRegisters : Fin 7↪Fin 32 := ⟨![13,14,12,11,4,5,6],by decide⟩

/-- `lem:print`, paper/paper.tex: actual Stack
formatting reads the same persistent stride, row-field, support-cardinal
and tuple-count registers after the reverse support loop finishes. -/
def kernelStackRegisters : Fin 8↪Fin 32 := ⟨![0,1,2,3,12,11,16,14],by decide⟩

/-- `prop:time`, paper/paper.tex: a fixed actual
bank width large enough for every called program is obtained from
those programs' own finite tape counts, independently of input size. -/
noncomputable def kernelSpan (native : Program) : ℕ :=
  native.tapeCount+supportIndexWordFunction.program.tapeCount+
    coefficientWordFunction.program.tapeCount+tupleRecordPrinter.program.tapeCount+
    stackRecordPrinter.program.tapeCount

end NearQuarticWires.StageTuple
