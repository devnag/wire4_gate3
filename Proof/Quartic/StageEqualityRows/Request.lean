import Proof.Quartic.StagePrint.DownstreamTargets
import Proof.Quartic.StagePrint.NativeEqualityPrinter
import Proof.Quartic.StagePrint.CutCounterMachine

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageEqualityRows

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Expand.PolyTab
open StagePrint StagePrint.Downstream

def stream (r : NativeStreamRequest) : List Bool :=
  r.cuts.flatMap (MatrixScoreBatch.cutWord r.fieldWidth)

def width (r : NativeStreamRequest) : ℕ := PrimT.C4Geo.width r.parameters

def loadCost (r : NativeStreamRequest) : ℕ :=
  Top.loadCost (stream r) (List.replicate (width r) true)
    (List.replicate r.fieldWidth true) [] [] [] [] [] [] [] []

def loadCapacity (r : NativeStreamRequest) : ℕ :=
  2*(equalityRowsInput r).length+1+
    Top.loadChainCost (stream r) (List.replicate (width r) true)
      (List.replicate r.fieldWidth true) [] [] [] [] [] [] [] []

def fields (r : NativeStreamRequest) : Fin 13 → List Bool :=
  ![frame (equalityRowsInput r),equalityRowsInput r,stream r,
    List.replicate (width r) true,List.replicate r.fieldWidth true,[],[],[],[],[],[],[],[]]

def loadMap (i : Fin 14) : Fin 16 := i.castAdd 2

def lens (r : NativeStreamRequest) (i : Fin 16) : ℕ := if i.val=13 then loadCapacity r else 0

def loaded (r : NativeStreamRequest) : WState 15 24 :=
  ⟨fun _=>0,fun i=>if h:i.val<13 then fields r ⟨i.val,h⟩ else List.replicate (lens r i) false,
    fun _=>0,false⟩

/-- `lem:print`, paper/paper.tex: the original
field stream has its literal dense-coordinate stride, without a count
or coefficient-magnitude input. -/
theorem cut_length (r : NativeStreamRequest) (c : MatrixScoreBatch.Cut) (hc : c∈r.cuts) :
    (MatrixScoreBatch.cutWord r.fieldWidth c).length=(2*width r+2)*(2*r.fieldWidth+3) := by
  obtain ⟨hl,hr⟩:=r.lengths c hc
  simp only [MatrixScoreBatch.cutWord,MatrixScoreBatch.fields,List.length_flatMap,
    List.map_append,List.sum_append,List.length_append,MatrixScoreBatch.signMagnitude_length,
    frame_length,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  simp only [List.map_const',List.sum_replicate]
  unfold width
  rw [hl,hr]
  ring

/-- `lem:print`, paper/paper.tex: the actual
stream size is its original cut census times its fixed field stride. -/
theorem stream_length (r : NativeStreamRequest) :
    (stream r).length=r.cuts.length*((2*width r+2)*(2*r.fieldWidth+3)) := by
  unfold stream
  rw [List.length_flatMap]
  have h : r.cuts.map (fun c=>(MatrixScoreBatch.cutWord r.fieldWidth c).length)=
      r.cuts.map (fun _=>(2*width r+2)*(2*r.fieldWidth+3)) := by
    apply List.map_congr_left
    intro c hc
    exact cut_length r c hc
  rw [h]
  simp

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual equality census is bounded by its own
serialized stream, including the empty stream. -/
theorem count_le_stream (r : NativeStreamRequest) : r.cuts.length≤(stream r).length := by
  rw [stream_length]
  have h : 1≤(2*width r+2)*(2*r.fieldWidth+3) := by nlinarith
  simpa using Nat.mul_le_mul_left r.cuts.length h

end NearQuarticWires.StageEqualityRows
