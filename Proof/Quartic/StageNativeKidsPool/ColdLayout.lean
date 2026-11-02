import Proof.Quartic.StageNativeKidsPool.Loop
import Proof.Quartic.StageNativeKidsPool.Families
import Proof.Wire_3_5.CompilerMachineTopLoad

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageNativeKidsPool
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close NearCubicGates.Close.WordPrograms
open NearQuarticWires.Control

/-- `lem:print`, paper/paper.tex: the
complete cold pool has separate finite load, actual counter and reusable
original-row banks, with one raw accumulator and one final frame. -/
def streams (counter row : Program) : ℕ:=counter.tapeCount+row.tapeCount+20

/-- `lem:print`, paper/paper.tex: the
actual fixed eleven-field source is loaded without changing any codec. -/
def loadMap (counter row : Program) (i : Fin 14) : Fin (streams counter row+1) :=
  ⟨i.val,by have:=i.isLt;unfold streams;omega⟩

/-- `lem:print`, paper/paper.tex: the
one actual original-record counter has its own paid source-copy bank. -/
def counterMap (counter row : Program) (i : Fin counter.tapeCount) : Fin (streams counter row+1) :=
  ⟨20+i.val,by have:=i.isLt;unfold streams;omega⟩

/-- `lem:print`, paper/paper.tex: every
actual row call uses one separate reusable ordinary-machine bank. -/
def rowMap (counter row : Program) (i : Fin row.tapeCount) : Fin (streams counter row+1) :=
  ⟨20+counter.tapeCount+i.val,by have:=i.isLt;unfold streams;omega⟩

/-- `lem:print`, paper/paper.tex: four
fixed row-call scalar slots lie outside all original-child counters. -/
def callRegisters : Fin 4 ↪ Fin 16:=
  ⟨fun i=>⟨i.val,by have:=i.isLt;omega⟩,by intro i j h;apply Fin.ext;exact congrArg (fun x : Fin 16=>x.val) h⟩

/-- `lem:print`, paper/paper.tex: the
runtime original-child index and its four formatting scratch slots are
distinct from the reusable-call and remaining-count scalar slots. -/
def rowRegisters : Fin 5 ↪ Fin 16:=
  ⟨fun i=>⟨4+i.val,by have:=i.isLt;omega⟩,by
    intro i j h;apply Fin.ext;have hv:=congrArg Fin.val h;simp only [Fin.val_mk] at hv;omega⟩

/-- `lem:print`, paper/paper.tex: the
original-row reusable call site is separate from the counter computation,
load fields, raw native accumulator and fresh final output tape. -/
def rowSite (counter row : Program) : Site row (streams counter row) 16 where
  bank:=rowMap counter row
  tally:=⟨17,by unfold streams;omega⟩
  guard:=⟨18,by unfold streams;omega⟩
  ruler:=⟨19,by unfold streams;omega⟩
  regs:=callRegisters
  bank_inj:=by
    intro i j h;apply Fin.ext;have hv:=congrArg Fin.val h;simp only [rowMap,Fin.val_mk] at hv;omega
  tally_ne:=by intro i h;have hv:=congrArg Fin.val h;change 20+counter.tapeCount+i.val=17 at hv;omega
  guard_ne:=by intro i h;have hv:=congrArg Fin.val h;change 20+counter.tapeCount+i.val=18 at hv;omega
  ruler_ne:=by intro i h;have hv:=congrArg Fin.val h;change 20+counter.tapeCount+i.val=19 at hv;omega
  tally_guard:=by intro h;have hv:=congrArg Fin.val h;change 17=18 at hv;omega
  tally_ruler:=by intro h;have hv:=congrArg Fin.val h;change 17=19 at hv;omega
  guard_ruler:=by intro h;have hv:=congrArg Fin.val h;change 18=19 at hv;omega

/-- `lem:print`, paper/paper.tex: the
retained original source and header are the actual first two loaded
fields; the only generated field is the next real row-call input. -/
def rowSources (counter row : Program) : Fin 3 ↪ Fin (streams counter row+1) :=
  ⟨fun i=>if i=0 then ⟨2,by unfold streams;omega⟩ else
    if i=1 then ⟨3,by unfold streams;omega⟩ else (rowSite counter row).input,by
    intro i j h
    fin_cases i <;> fin_cases j <;> try rfl
    all_goals have hv:=congrArg Fin.val h
    all_goals simp [rowSite,Site.input,rowMap,WorkerArith.inTape] at hv
    all_goals omega⟩

/-- `lem:print`, paper/paper.tex: the
complete counted raw-row loop has a concrete fixed source/register
layout, without any external row, count or geometry provider. -/
def rowLayout (counter row : Program) : Layout row (streams counter row) 16 where
  site:=rowSite counter row
  sources:=rowSources counter row
  registers:=rowRegisters
  out:=⟨14,by unfold streams;omega⟩
  outputCounter:=10
  remaining:=9
  input_eq:=by simp [rowSources]
  out_bank:=by intro i h;have hv:=congrArg Fin.val h;change 20+counter.tapeCount+i.val=14 at hv;omega
  out_tally:=by intro h;have hv:=congrArg Fin.val h;change 14=17 at hv;omega
  out_guard:=by intro h;have hv:=congrArg Fin.val h;change 14=18 at hv;omega
  out_ruler:=by intro h;have hv:=congrArg Fin.val h;change 14=19 at hv;omega
  out_sources:=by
    intro i h
    have hv:=congrArg Fin.val h
    fin_cases i <;> simp [rowSources,rowSite,Site.input,rowMap,WorkerArith.inTape] at hv
    all_goals omega
  counter_registers:=by intro i;fin_cases i <;> decide
  counter_call:=by intro i;change (10 : Fin 16)≠callRegisters i;fin_cases i <;> decide
  remaining_registers:=by intro i;fin_cases i <;> decide
  remaining_call:=by intro i;change (9 : Fin 16)≠callRegisters i;fin_cases i <;> decide
  index_call:=by intro i;change (4 : Fin 16)≠callRegisters i;fin_cases i <;> decide
  remaining_output:=by decide

end NearQuarticWires.StageNativeKidsPool
