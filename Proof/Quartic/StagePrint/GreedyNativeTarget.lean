import Proof.Quartic.StagePrint.GreedyCollectorTarget
import Proof.Quartic.StageRecovery.NativeRequest

set_option autoImplicit false

namespace NearQuarticWires.StagePrint.GreedyNative
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5
open NearCubicGates.Close.Interfaces

/-- `lem:print`, paper/paper.tex: one actual
whole-walk native table keeps every reduced weak cut in its original
order and uses the original common generator and prefix convention. -/
structure Data {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) where
  native : StageRecovery.NativeRequest
  dimension_eq : native.table.matrix.d=PrimT.C4Geo.dRow (GreedyCollector.star r)
  width_eq : native.table.matrix.width=PrimT.C4Geo.width (GreedyCollector.star r)
  fieldWidth_eq : native.table.matrix.p=GreedyCollector.fieldWidth r
  columns_eq : ∀ j,native.table.matrix.column j=(PrimT.C4Geo.cols (GreedyCollector.star r)).getD j 0
  cuts_eq : native.table.matrix.cuts=(List.ofFn (GreedyCollector.walkCuts r)).flatten
  modulus_eq : native.modulus=r.prime^r.child.selected.1.e
  targetCount_eq : native.targetCount=r.child.cellCall.ncol
  output_eq : native.output=listWord NearCubicGates.Close.Interfaces.intWord (Greedy.printTable r)

/-- `lem:print`, paper/paper.tex: the actual
whole table docks directly to the existing physical native-header
printer, with all shape and common-generator fields proved. -/
def Data.headerRequest {B1 B2 : ℕ} {r : Greedy.PrintRequest B1 B2} (data : Data r) :
    Downstream.NativeHeaderRequest where
  parameters:=GreedyCollector.star r
  table:=data.native.table
  dimension_eq:=data.dimension_eq
  width_eq:=data.width_eq
  columns_eq:=data.columns_eq

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual original source alone constructs the whole
typed table and proves its native field heights polynomial; no table,
child, coefficient, count or geometric model is an additional input. -/
abbrev Supplier (B1 B2 : ℕ) :=
  {data : (r : Greedy.PrintRequest B1 B2)→Data r //
    ∃ C E : ℕ,∀ r : Greedy.PrintRequest B1 B2,
      (data r).native.table.matrix.p+(data r).native.table.q+
        NearCubicWires.natBitLength (data r).native.modulus≤C*(r.child.call.n+1)^E}

end NearQuarticWires.StagePrint.GreedyNative
