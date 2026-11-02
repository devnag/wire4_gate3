import Proof.Quartic.StagePrintTuple.Request
import Proof.Quartic.StagePrint.CutFieldCodec

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.ThresholdCompiler
open NearCubicWires.SupplierPipeline
open NearCubicGates.Close.Tabulator NearCubicGates.Close.TabMachine
open NearCubicWires.WireExponent3_5

/-- `imp:pullback` and `lem:print`, paper/paper.tex: a native exact gate is the same weighted equality in the equation representation. -/
def equationOfNativeGate {n : ℕ} (e : ExactThresholdGate n) : ExactEquation n :=
  ⟨e.weight,e.target⟩

/-- `lem:print`, paper/paper.tex: the two native halves contain exactly the original routed coordinate fields, with their common padding. -/
def nativeDimension (r : StageTuple.RowContext) : ℕ :=
  PrimT.C4Geo.width r.header.prepared.starParams+PrimT.C4Geo.width r.header.prepared.starParams

abbrev NativeHalfEquation (r : StageTuple.RowContext) :=
  RowBinLift.Equation ((nativeDimension r+1)/2) (nativeDimension r/2)

/-- `imp:disjoint`, `imp:pullback` and `lem:print`, paper/paper.tex: typed native equations follow the ORIGINAL sharp child order at the actual canonical walk role. -/
def nativeKidsEquations (r : StageTuple.RowContext)
    (i : Fin (17*(Builder.allGates r.header.call).length)) : List (NativeHalfEquation r) :=
  List.ofFn fun j : Fin (exactChildren (callAtoms r.header.call (r.originalIndex i))).length =>
    toHalves (equationOfNativeGate (r.originalRow i j).nativeChild)

/-- `lem:print`, paper/paper.tex: the typed equality pool and actual row printer have identical signed field lists in identical child order. -/
theorem nativeKidsEquations_fields (r : StageTuple.RowContext)
    (i : Fin (17*(Builder.allGates r.header.call).length)) :
    (nativeKidsEquations r i).map eqF=r.nativeKids i := by
  unfold nativeKidsEquations StageTuple.RowContext.nativeKids
  rw [List.map_ofFn]
  congr 1
  funext j
  exact eqF_toHalves (equationOfNativeGate (r.originalRow i j).nativeChild)

/-- `lem:print`, paper/paper.tex: literal tuple stacking emits exactly the corresponding typed weighted equation word, before the two weak-cut split. -/
theorem packedNativeCut_word {s : ℕ} (W : ℕ) (coefficient : ℤ)
    (es : List (RowBinLift.Equation ((s+1)/2) (s/2))) :
    MatrixScoreBatch.cutWord W (RowBinLift.split coefficient (SupplierEstimator.canonicalEquationStack es))=
      cutRecs W s coefficient (es.map eqF) := by
  unfold MatrixScoreBatch.cutWord cutRecs
  rw [fields_cut]
  apply List.flatMap_congr
  intro z hz
  change frame (MatrixScoreBatch.signMagnitude W z)=
    frame (SignedSortKey.binary (W+1) (NearCubicGates.Close.WordPrograms.SInt.encS z))
  exact congrArg frame (binary_encS_signMagnitude W z).symm

/-- `lem:print`, paper/paper.tex: a monomial's exact equation cuts use the actual same-phi child pools and original lexicographic tuple order. -/
def nativeEqualityCuts (r : StageTuple.TermCutRequest) : List MatrixScoreBatch.Cut :=
  r.terms.flatMap fun t =>
    (tuples ((t.1.sort (· ≤ ·)).map (nativeKidsEquations r.toRowContext))).map fun es =>
      RowBinLift.split t.2 (SupplierEstimator.canonicalEquationStack es)

/-- `lem:print`, paper/paper.tex: the actual tuple/stack output is byte-for-byte the typed native equality stream on the same common phi. -/
theorem nativeEqualityCuts_word (r : StageTuple.TermCutRequest) :
    (nativeEqualityCuts r).flatMap (MatrixScoreBatch.cutWord r.stackWidth)=r.output := by
  simp only [nativeEqualityCuts,StageTuple.TermCutRequest.output,List.flatMap_assoc,List.flatMap_map]
  apply List.flatMap_congr
  intro t ht
  have hp : (t.1.sort (· ≤ ·)).map r.toRowContext.nativeKids=
      ((t.1.sort (· ≤ ·)).map (nativeKidsEquations r.toRowContext)).map (List.map eqF) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro i hi
    exact (nativeKidsEquations_fields r.toRowContext i).symm
  rw [hp,tuples_map,List.flatMap_map]
  apply List.flatMap_congr
  intro es hes
  have hd : r.rowDimension=nativeDimension r.toRowContext:=by
    unfold StageTuple.TermCutRequest.rowDimension nativeDimension
    omega
  rw [hd]
  exact packedNativeCut_word r.stackWidth t.2 es

/-- `lem:print`, paper/paper.tex: every typed equality cut has exactly the actual two routed native half-widths. -/
theorem nativeEqualityCuts_lengths (r : StageTuple.TermCutRequest) :
    ∀ c ∈ nativeEqualityCuts r,
      c.leftWeights.length=PrimT.C4Geo.width r.header.prepared.starParams ∧
      c.rightWeights.length=PrimT.C4Geo.width r.header.prepared.starParams := by
  intro c hc
  obtain ⟨t,ht,hc⟩:=List.mem_flatMap.mp hc
  obtain ⟨es,hes,rfl⟩:=List.mem_map.mp hc
  simp only [RowBinLift.split,List.length_ofFn]
  unfold nativeDimension
  omega

end NearQuarticWires.StagePrint
