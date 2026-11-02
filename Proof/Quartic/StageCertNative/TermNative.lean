import Proof.Quartic.StageCertNative.Table
import Proof.Quartic.StageCertNative.TermJob
import Proof.Quartic.StagePrint.DownstreamTargets

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5

/-- `lem:print`, paper/paper.tex: a single
term's equality list is part of the actual concatenated whole test. -/
theorem termCuts_length_le_whole {B1 B2 : ℕ} (r : TermJob B1 B2) :
    (StagePrint.nativeEqualityCuts (termRequest r.base r.index)).length≤
      (wholeCuts r.base).length := by
  unfold wholeCuts
  rw [List.length_flatten]
  apply List.single_le_sum (fun _ _=>Nat.zero_le _)
  apply List.mem_map_of_mem
  exact List.mem_ofFn.mpr ⟨r.index,rfl⟩

/-- `lem:print`, paper/paper.tex: the per-term
two-weak-cut conversion has the same original geometry and actual
uniform field width as the eventual single whole-test table. -/
noncomputable def termNativeRequest {B1 B2 : ℕ} (r : TermJob B1 B2) :
    StagePrint.NativeStreamRequest where
  parameters:=r.moment.rules.starParams
  fieldWidth:=(termRequest r.base r.index).stackWidth
  cuts:=StagePrint.nativeEqualityCuts (termRequest r.base r.index)
  lengths:=StagePrint.nativeEqualityCuts_lengths (termRequest r.base r.index)
  fits:=StageNativeWidth.nativeEqualityCuts_fits (termRequest r.base r.index)
  square:=by
    have hh:=Nat.mul_le_mul_left 2 (termCuts_length_le_whole r)
    exact (Nat.mul_le_mul hh hh).trans (wholeCuts_square r.base)

noncomputable def termWeakWord {B1 B2 : ℕ} (r : TermJob B1 B2) : List Bool :=
  (EquationRow.doubled false (termNativeRequest r).cuts).flatMap
    (MatrixScoreBatch.cutWord ((termNativeRequest r).fieldWidth+1))

end NearQuarticWires.StageCertNative
