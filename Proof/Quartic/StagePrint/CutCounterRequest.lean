import Proof.Quartic.StagePrint.NativeCutCount
import Proof.Quartic.StagePrint.UnaryRegister
import Proof.Gates.Expand.PolyTabPack
import Proof.Wire_3_5.CompilerMachineTopLoad

set_option autoImplicit false

namespace NearQuarticWires.StagePrint.CutCounter

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.Expand.PolyTab

/-- `lem:print`, paper/paper.tex: the cold
counter reads the actual cut stream and its dense half-width,
without an input equality count or signed coefficient magnitudes. -/
structure Request where
  width : ℕ
  fieldWidth : ℕ
  cuts : List MatrixScoreBatch.Cut
  lengths : ∀ c∈cuts,c.leftWeights.length=width ∧ c.rightWeights.length=width

def Request.stride (r : Request) : ℕ := 2*r.width+2
def Request.stream (r : Request) : List Bool := r.cuts.flatMap (MatrixScoreBatch.cutWord r.fieldWidth)
def Request.unaryStride (r : Request) : List Bool := List.replicate r.stride true

/-- `lem:print`, paper/paper.tex: the two
actual framed fields contain the unchanged cut bytes and a polynomial
dense-coordinate stride; the remaining loader fields are empty. -/
def Request.word (r : Request) : List Bool :=
  Top.loadRec r.stream r.unaryStride [] [] [] [] [] [] [] [] []

def Request.loadCost (r : Request) : ℕ :=
  Top.loadCost r.stream r.unaryStride [] [] [] [] [] [] [] [] []

def Request.loadCapacity (r : Request) : ℕ :=
  2*r.word.length+1+Top.loadChainCost r.stream r.unaryStride [] [] [] [] [] [] [] [] []

def Request.fields (r : Request) : Fin 13→List Bool :=
  ![frame r.word,r.word,r.stream,r.unaryStride,[],[],[],[],[],[],[],[],[]]

def loadMap (i : Fin 14) : Fin 16 := i.castAdd 2

def Request.lens (r : Request) (i : Fin 16) : ℕ := if i.val=13 then r.loadCapacity else 0

def Request.loaded (r : Request) : WState 15 24 :=
  ⟨fun _=>0,fun i=>if h:i.val<13 then r.fields ⟨i.val,h⟩ else List.replicate (r.lens i) false,
    fun _=>0,false⟩

def countRegisters : Fin 6 ↪ Fin 24 :=
  ⟨fun i=>i.castAdd 18,by intro i j h;apply Fin.ext;exact congrArg (fun x : Fin 24=>x.val) h⟩

def writeRegisters : Fin 8 ↪ Fin 24 :=
  ⟨![5,7,8,9,10,11,12,13],by decide⟩

/-- `prop:time`, paper/paper.tex: all register
capacity is linear in the actual stream and count, rather than in
the magnitudes represented by its signed fields. -/
def Request.capacity (r : Request) : ℕ :=
  r.loadCapacity+r.stream.length+r.stride+20*(r.cuts.length+1)+100

end NearQuarticWires.StagePrint.CutCounter
