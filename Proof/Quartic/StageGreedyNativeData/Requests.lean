import Proof.Quartic.StageGreedyNativeData.Census
import Proof.Quartic.StageGreedyCollector.Requests

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyNativeData

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.SourceInterfaces
open NearCubicWires.WireExponent3_5
open StagePrint

/-- `lem:print`, paper/paper.tex: the original
global equality stream uses the same packed width on every walk. -/
noncomputable def equalityStream {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    NativeStreamRequest where
  parameters:=GreedyCollector.star r
  fieldWidth:=GreedyCollector.fieldWidth r-1
  cuts:=equalityCuts r
  lengths:=by
    intro c hc
    obtain ⟨cs,hcs,hc⟩:=List.mem_flatten.mp hc
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hcs
    exact nativeEqualityCuts_lengths (GreedyEntry.Request.termRequest ⟨r,i⟩) c hc
  fits:=by
    intro c hc
    obtain ⟨cs,hcs,hc⟩:=List.mem_flatten.mp hc
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hcs
    have h:=StageNativeWidth.nativeEqualityCuts_fits
      (GreedyEntry.Request.termRequest ⟨r,i⟩) c hc
    simpa only [←GreedyEntry.Request.fieldWidth_eq ⟨r,i⟩,Nat.add_sub_cancel] using h
  square:=equalityCuts_square r

theorem equalityStream_fieldWidth {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    (equalityStream r).matrix.p=GreedyCollector.fieldWidth r := by
  change GreedyCollector.fieldWidth r-1+1=GreedyCollector.fieldWidth r
  have h : 1 ≤ GreedyCollector.fieldWidth r := by
    unfold GreedyCollector.fieldWidth
    omega
  omega

theorem equalityStream_modulus_fit {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    r.prime^r.child.selected.1.e ≤ 2^(equalityStream r).matrix.p := by
  rw [equalityStream_fieldWidth]
  exact (StageGreedyCollector.modularRequest
    (GreedyEntry.Request.mk r ⟨0,StageLiftSourceCost.walkCount_pos r⟩)).modulus_fit

/-- `lem:print`, paper/paper.tex: coefficient
reduction follows the signed two-weak split of the actual global
equality stream, retaining its common original generator. -/
noncomputable def table {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) : TableRequest where
  matrix:=StageRecovery.reduceRequest (equalityStream r).matrix
    (r.prime^r.child.selected.1.e) (equalityStream r).matrix.p le_rfl
    (GreedyEntry.Request.modulus_pos ⟨r,⟨0,StageLiftSourceCost.walkCount_pos r⟩⟩)
    (equalityStream_modulus_fit r)
  cuts_le:=by
    change ((equalityStream r).matrix.cuts.map
      (StageRecovery.reduceCut (r.prime^r.child.selected.1.e))).length ≤ (equalityStream r).matrix.U
    rw [List.length_map]
    exact (equalityStream r).table.cuts_le

theorem table_cuts {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    (table r).matrix.cuts=(List.ofFn (GreedyCollector.walkCuts r)).flatten := by
  change (EquationRow.doubled false (equalityCuts r)).map
    (StageRecovery.reduceCut (r.prime^r.child.selected.1.e))=
    (List.ofFn fun i : Fin (r.child.cellCall.seed.N^8) =>
      (EquationRow.doubled false (nativeEqualityCuts
        (GreedyEntry.Request.termRequest ⟨r,i⟩))).map
          (StageRecovery.reduceCut (r.prime^r.child.selected.1.e))).flatten
  simp only [equalityCuts,EquationRow.doubled,List.flatMap_def,List.map_flatten,
    List.map_map,List.map_ofFn,Function.comp_def,List.flatten_flatten]

theorem table_columns {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    (table r).matrix.cols=PrimT.C4Geo.cols (GreedyCollector.star r) :=
  (equalityStream r).matrix_columns

theorem table_nonnegative {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    ∀ c∈(table r).matrix.cuts,0 ≤ c.coefficient := by
  intro c hc
  obtain ⟨d,hd,rfl⟩:=List.mem_map.mp hc
  exact StageRecovery.reduceCut_nonneg _
    (GreedyEntry.Request.modulus_pos ⟨r,⟨0,StageLiftSourceCost.walkCount_pos r⟩⟩) d

theorem targetCount_le {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    r.child.cellCall.ncol ≤ (table r).count := by
  let hs:=Cells.prepare_spec _ r.child.selected.1 r.child.selected.2
  change 2^(r.child.call.n-r.child.selected.1.k) ≤
    2^PrimT.C4Geo.dRow hs.starParams*2^PrimT.C4Geo.dRow hs.starParams
  rw [←pow_add,Builder.centerCount_eq r.child.call hs]
  exact Nat.pow_le_pow_right (by decide) (Nat.add_le_add_left hs.starParams.centerBits_balanced.1 _)

/-- `lem:print` and `lem:residue`, paper/paper.tex: the actual complete native table and the original
column count determine the unique centered-prefix recovery request. -/
noncomputable def nativeRequest {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    StageRecovery.NativeRequest where
  table:=table r
  modulus:=r.prime^r.child.selected.1.e
  modulus_pos:=GreedyEntry.Request.modulus_pos ⟨r,⟨0,StageLiftSourceCost.walkCount_pos r⟩⟩
  nonnegative:=table_nonnegative r
  targetCount:=r.child.cellCall.ncol
  targetCount_le:=targetCount_le r

end NearQuarticWires.StageGreedyNativeData
