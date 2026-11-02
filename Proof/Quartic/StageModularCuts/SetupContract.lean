import Proof.Quartic.StageModularCuts.KernelData
import Proof.Quartic.StagePrint.DownstreamTargets
import Proof.Gates.Expand.PolyTabPack
import Proof.Wire_3_5.CompilerMachineTopLoad

set_option autoImplicit false

namespace NearQuarticWires.StageModularCuts.Setup

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Expand.PolyTab
open StagePrint.Downstream

abbrev Request := ModularCutsRequest

def scale (r : Request) : ℕ := r.width + r.fieldWidth + natBitLength r.modulus + 2

def loadCost (r : Request) : ℕ :=
  Top.loadCost (natWord r.modulus) r.stream (List.replicate r.fieldWidth true)
    (List.replicate r.width true) [] [] [] [] [] [] []

def loadCapacity (r : Request) : ℕ :=
  2 * r.word.length + 1 +
    Top.loadChainCost (natWord r.modulus) r.stream (List.replicate r.fieldWidth true)
      (List.replicate r.width true) [] [] [] [] [] [] []

def lens (r : Request) (i : Fin 16) : ℕ := if i.val = 13 then loadCapacity r else 0

/-- `lem:print`, paper/paper.tex: the loaded source
retains the exact signed weak-cut stream and binary modulus encoding. -/
def fields (r : Request) : Fin 13 → List Bool :=
  ![frame r.word, r.word, natWord r.modulus, r.stream,
    List.replicate r.fieldWidth true, List.replicate r.width true,
    [], [], [], [], [], [], []]

def loaded (r : Request) : State :=
  ⟨fun _ => 0, fun i => if h : i.val < 13 then fields r ⟨i.val, h⟩
    else List.replicate (lens r i) false, fun _ => 0, false⟩

/-- `lem:print`, paper/paper.tex: binary setup uses
one extra work bit, including when the modulus equals `2^fieldWidth`.
Only the widths, rather than any encoded coefficient, enter registers. -/
def ready (r : Request) : State :=
  let W := r.fieldWidth + 1
  let a := (loaded r).sets coefficient (frame (binary W 0))
  let a := a.sets modulus (frame (binary W r.modulus))
  let a := a.sets magnitude (frame (binary W 0))
  let a := a.sets quotient (frame (binary W 0))
  let a := a.sets remainder (frame (binary W 0))
  let a := a.sets temporary (frame (binary W 0))
  (a.setv 7 W).setv 8 (2 * r.width + 1)

/-- `prop:time`, paper/paper.tex: the workspace
capacity is linear in the serialized cut stream and polynomial in widths. -/
def capacity (r : Request) : ℕ := 10 ^ 8 * (scale r) ^ 8 * (r.stream.length + 1)

def clock (r : Request) : ℕ := loadCost r + 10 ^ 6 * (scale r) ^ 4

/-- `lem:print` and `prop:time`, paper/paper.tex: a cold setup execution physically loads the actual source,
decodes the binary modulus, and initializes the bounded work tapes. -/
def SetupSpec (P : Program) : Prop :=
  ∀ r : Request, WXExec (capacity r) P
    (idealStart 15 16 r.word (lens r)) (ready r) (clock r)

end NearQuarticWires.StageModularCuts.Setup
