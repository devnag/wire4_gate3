import Proof.Quartic.StagePrint.NativeRequests
import Proof.Quartic.StagePrint.PacketInterface
import Proof.Quartic.StageRecovery.Coefficients

set_option autoImplicit false

namespace NearQuarticWires.StagePrint.Downstream

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Interfaces.Formats

/-- `lem:print`, paper/paper.tex: cold projection
from the actual exact formatted packet to its original signed Formula. -/
abbrev ExactPacketProjection :=
  WordFunction PacketInterface.ExactProjectionRequest PacketInterface.ExactProjectionRequest.word
    (fun r=>frame (formulaWord r.formula)) (fun r=>10^8*(r.word.length+1)^2)

/-- `lem:print`, paper/paper.tex: the row
constructor receives actual bytes and polynomial unary widths,
without a supplied equality count. -/
def equalityRowsInput (r : NativeStreamRequest) : List Bool :=
  Top.loadRec (r.cuts.flatMap (MatrixScoreBatch.cutWord r.fieldWidth))
    (List.replicate (PrimT.C4Geo.width r.parameters) true)
    (List.replicate r.fieldWidth true) [] [] [] [] [] [] [] []

def equalityRowsOutput (r : NativeStreamRequest) : List Bool :=
  frame ((EquationRow.doubled false r.cuts).flatMap (MatrixScoreBatch.cutWord (r.fieldWidth+1)))

/-- `lem:print` and `prop:time`, paper/paper.tex: one actual per-walk cold constructor measures count,
makes the two weak cuts and removes its temporary header. -/
abbrev EqualityRowsPrinter :=
  WordFunction NativeStreamRequest equalityRowsInput equalityRowsOutput
    (fun r=>10^30*(PrimT.C4Geo.width r.parameters+r.fieldWidth+2)^20*
      ((r.cuts.flatMap (MatrixScoreBatch.cutWord r.fieldWidth)).length+1)^2)

/-- `lem:residue` and `lem:print`, paper/paper.tex: reduction acts on actual signed weak cuts after
the equality split and leaves every affine predicate unchanged. -/
structure ModularCutsRequest where
  width : ℕ
  fieldWidth : ℕ
  modulus : ℕ
  cuts : List MatrixScoreBatch.Cut
  modulus_two : 2 ≤ modulus
  modulus_fit : modulus ≤ 2^fieldWidth
  lengths : ∀ c∈cuts,c.leftWeights.length=width ∧ c.rightWeights.length=width
  fits : ∀ c∈cuts,EquationRow.Fits fieldWidth c

def ModularCutsRequest.stream (r : ModularCutsRequest) : List Bool :=
  r.cuts.flatMap (MatrixScoreBatch.cutWord r.fieldWidth)

def ModularCutsRequest.word (r : ModularCutsRequest) : List Bool :=
  Top.loadRec (natWord r.modulus) r.stream (List.replicate r.fieldWidth true)
    (List.replicate r.width true) [] [] [] [] [] [] []

def ModularCutsRequest.output (r : ModularCutsRequest) : List Bool :=
  frame ((r.cuts.map (StageRecovery.reduceCut r.modulus)).flatMap (MatrixScoreBatch.cutWord r.fieldWidth))

/-- `lem:residue`, `lem:print` and `prop:time`, paper/paper.tex: modular coefficient
reduction is linear in the number of encoded signed rows. -/
abbrev ModularCutsPrinter :=
  WordFunction ModularCutsRequest ModularCutsRequest.word ModularCutsRequest.output
    (fun r=>10^30*(r.width+r.fieldWidth+natBitLength r.modulus+2)^20*(r.stream.length+1))

/-- `lem:print`, paper/paper.tex: the actual
weak-cut table has the original canonical star generator. The
relations here are proof-only; no columns or count occur in its source. -/
structure NativeHeaderRequest where
  parameters : Shared.StarParams
  table : TableRequest
  dimension_eq : table.matrix.d=PrimT.C4Geo.dRow parameters
  width_eq : table.matrix.width=PrimT.C4Geo.width parameters
  columns_eq : ∀ j,table.matrix.column j=(PrimT.C4Geo.cols parameters).getD j 0

def NativeHeaderRequest.stream (r : NativeHeaderRequest) : List Bool :=
  r.table.matrix.cuts.flatMap (MatrixScoreBatch.cutWord r.table.matrix.p)

def NativeHeaderRequest.word (r : NativeHeaderRequest) : List Bool :=
  [r.parameters.n,r.parameters.r,r.parameters.b,r.parameters.s,r.table.matrix.p].flatMap natWord++r.stream

/-- `lem:print` and `prop:time`, paper/paper.tex: cold header assembly computes the real cut census
and canonical columns and writes the exact native table request. -/
abbrev NativeHeaderPrinter :=
  WordFunction NativeHeaderRequest NativeHeaderRequest.word (fun r=>frame r.table.word)
    (fun r=>10^30*(r.parameters.n+r.table.matrix.p+2)^20*(r.stream.length+r.table.count+1))

#check ExactPacketProjection
#check EqualityRowsPrinter
#check ModularCutsPrinter
#check NativeHeaderPrinter

end NearQuarticWires.StagePrint.Downstream
