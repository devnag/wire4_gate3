import Proof.Quartic.StageGreedyNativeData.Output
import Proof.Quartic.StageGreedyNativeData.Widths

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyNativeData

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open StagePrint

/-- `lem:print`, paper/paper.tex: the complete
actual original-walk native data includes the proved global capacity,
common Phi, original-column count and exact recovered output. -/
noncomputable def nativeData {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    GreedyNative.Data r where
  native:=nativeRequest r
  dimension_eq:=rfl
  width_eq:=rfl
  fieldWidth_eq:=equalityStream_fieldWidth r
  columns_eq:=fun _=>rfl
  cuts_eq:=table_cuts r
  modulus_eq:=rfl
  targetCount_eq:=rfl
  output_eq:=native_output r

/-- `lem:print` and `prop:time`, paper/paper.tex: the global original Greedy native supplier
is unconditional, with both actual widths polynomial in original arity. -/
noncomputable def nativeSupplier (B1 B2 : ℕ) : GreedyNative.Supplier B1 B2 :=
  ⟨nativeData,native_widths_bound B1 B2⟩

/-- `lem:print`, paper/paper.tex: the supplier
consumes exactly the frozen collector's five headers and unchanged
concatenated weak stream, without an extra model or count field. -/
theorem header_word_eq {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    ((nativeSupplier B1 B2).val r).headerRequest.word=GreedyCollector.word r := by
  change [_,_,_,_,(table r).matrix.p].flatMap natWord++
    (table r).matrix.cuts.flatMap (MatrixScoreBatch.cutWord (table r).matrix.p)=_
  rw [show (table r).matrix.p=GreedyCollector.fieldWidth r from equalityStream_fieldWidth r,table_cuts]
  change _ = [_,_,_,_,_].flatMap natWord++_
  congr 1
  simp only [GreedyCollector.stream,List.flatMap_def,List.map_flatten,List.map_ofFn,
    Function.comp_def,List.flatten_flatten]

end NearQuarticWires.StageGreedyNativeData
