import Proof.Quartic.StagePrintTuple.RowFields
import Proof.Quartic.StagePrint.StackPrinter
import Proof.Quartic.StagePrint.CutFieldCodec

set_option autoImplicit false

namespace NearQuarticWires.StagePrint.NativeWidth
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.TabMachine

/-- `lem:print`, paper/paper.tex: one width simultaneously accommodates signed source fields, packing radix powers and the polynomial coefficient. -/
def packedBits (L s D cbits : ℕ) : ℕ :=
  max cbits ((D+2)*(L+s+D+4))+4

/-- `imp:pullback` and `lem:print`, paper/paper.tex: exact decoding of the physically emitted native source field requires this original-request bound. -/
def SourceFits (r : StagePullback.RowRequest) : Prop :=
  ∀ z ∈ List.ofFn (StagePullback.NativeRows.nativeChild r.point r.child r.transpose).weight ++
    [(StagePullback.NativeRows.nativeChild r.point r.child r.transpose).target],
    SInt.encS z<2^r.Lout

/-- `imp:pullback` and `lem:print`, paper/paper.tex: the actual seventeen-role child pools have their common output-field width. -/
def KidsFit (r : StageTuple.RowContext) : Prop :=
  ∀ i : Fin (17*(Builder.allGates r.header.call).length),
    ∀ row ∈ r.nativeKids i,∀ z ∈ row,SInt.encS z<2^r.nativeFieldWidth

/-- `lem:print`, paper/paper.tex: the packing and cut fields required by the actual StackRequest are controlled at each monomial's own degree. -/
def PackedFit (L s D cbits : ℕ) : Prop :=
  ∀ (ls : List (List ℤ)) (c : ℤ),ls.length≤ D →
    (∀ row ∈ ls,row.length=s+1 ∧ ∀ z ∈ row,SInt.encS z<2^L) → c.natAbs<2^cbits →
    (magL ls+1)^(ls.length+1)<2^(packedBits L s D cbits) ∧
      (∀ z ∈ cutL s c ls,SInt.encS z<2^(packedBits L s D cbits+1)) ∧
      (∀ z ∈ cutL s c ls,z.natAbs<2^(packedBits L s D cbits))

#check (fun (r : StagePullback.RowRequest) => SourceFits r)
#check (fun (r : StageTuple.RowContext) => KidsFit r)
#check (fun (L s D cbits : ℕ) => PackedFit L s D cbits)
#check NearCubicWires.RepairOrdinary.EquationRow.successor_fits
#check NearCubicGates.Close.Tabulator.stack_bound
#check NearQuarticWires.StageTuple.RowContext.originalRow_Lout_eq

end NearQuarticWires.StagePrint.NativeWidth
