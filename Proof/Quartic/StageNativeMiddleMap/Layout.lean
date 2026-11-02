import Proof.Quartic.StagePrint.NativeMiddleTarget
import Proof.Quartic.StagePrint.CallAppend
import Proof.Quartic.StagePrint.CallStates
import Proof.Quartic.StagePrintTuple.NaturalsReset
import Proof.Quartic.StageNativeKids.MarkedCopy
import Proof.Gates.Expand.PolyTabPack

set_option autoImplicit false

namespace NearQuarticWires.StageNativeMiddleMap

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearQuarticWires.Control
open NearCubicGates.Close.WordPrograms

/-- `lem:print`, paper/paper.tex: the fixed
record loader and all temporary streams lie outside the actual call bank. -/
def external (p : Program) (i : Fin 19) : Fin (p.tapeCount+20) := ⟨i.val,by omega⟩

def bank (p : Program) (j : Fin p.tapeCount) : Fin (p.tapeCount+20) := ⟨19+j.val,by omega⟩

def final (p : Program) : Fin (p.tapeCount+20) := ⟨p.tapeCount+19,by omega⟩

def loadMap (p : Program) (i : Fin 14) : Fin (p.tapeCount+20) := ⟨i.val,by omega⟩

theorem bank_external_ne (p : Program) (j : Fin p.tapeCount) (i : Fin 19) :
    bank p j≠external p i := by
  intro h
  have hh:=congrArg Fin.val h
  change 19+j.val=i.val at hh
  omega

theorem bank_injective (p : Program) : Function.Injective (bank p) := by
  intro i j h
  apply Fin.ext
  have hh:=congrArg Fin.val h
  change 19+i.val=19+j.val at hh
  omega

theorem loadMap_injective (p : Program) : Function.Injective (loadMap p) := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun x : Fin (p.tapeCount+20)=>x.val) h

theorem external_injective (p : Program) : Function.Injective (external p) := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun x : Fin (p.tapeCount+20)=>x.val) h

def site (p : Program) : Site p (p.tapeCount+19) 32 where
  bank:=bank p
  tally:=external p 14
  guard:=external p 15
  ruler:=external p 16
  regs:=⟨![0,1,2,3],by decide⟩
  bank_inj:=bank_injective p
  tally_ne:=fun j=>bank_external_ne p j 14
  guard_ne:=fun j=>bank_external_ne p j 15
  ruler_ne:=fun j=>bank_external_ne p j 16
  tally_guard:=fun h=>by have hh:=congrArg Fin.val h;change 14=15 at hh;omega
  tally_ruler:=fun h=>by have hh:=congrArg Fin.val h;change 14=16 at hh;omega
  guard_ruler:=fun h=>by have hh:=congrArg Fin.val h;change 15=16 at hh;omega

/-- `lem:print`, paper/paper.tex: the actual
loaded metadata retains encoded natural bytes, while the middle field
already holds the genuine cold input frame of the callee. -/
def fields (q : ℕ) (payload : List Bool) (count : ℕ) : Fin 13→List Bool :=
  ![frame (StagePrint.NativeMiddle.word q payload count),StagePrint.NativeMiddle.word q payload count,
    natWord q,frame payload,natWord count,[],[],[],[],[],[],[],[]]

def lens (p : Program) (cap : ℕ) (i : Fin (p.tapeCount+20)) : ℕ :=
  if i.val=13 then cap else 0

def loaded (p : Program) (cap q : ℕ) (payload : List Bool) (count : ℕ) :
    WState (p.tapeCount+19) 32 :=
  ⟨fun _=>0,fun i=>if h : i.val<13 then fields q payload count ⟨i.val,h⟩
    else if i.val=13 then List.replicate cap false else [],fun _=>0,false⟩

def loadCost (q : ℕ) (payload : List Bool) (count : ℕ) : ℕ :=
  Top.loadCost (natWord q) (frame payload) (natWord count) [] [] [] [] [] [] [] []

def chainCost (q : ℕ) (payload : List Bool) (count : ℕ) : ℕ :=
  Top.loadChainCost (natWord q) (frame payload) (natWord count) [] [] [] [] [] [] [] []

def prepared (p : Program) (cap q : ℕ) (payload : List Bool) (count : ℕ) :=
  (loaded p cap q payload count).sets (site p).input (frame payload)

def copied (p : Program) (cap q : ℕ) (input output : List Bool) (count : ℕ) :=
  appendO (loaded p cap q input count) (external p 18) (6 : Fin 32) (frame output)

def ready (p : Program) (cap q : ℕ) (input output : List Bool) (count : ℕ) :=
  ((copied p cap q input output count).setv 6 0).seth (external p 18) 0

end NearQuarticWires.StageNativeMiddleMap
