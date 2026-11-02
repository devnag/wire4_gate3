import Proof.Quartic.StageNativeWidth.SourceBounds

set_option autoImplicit false

namespace NearQuarticWires.StageNativeWidth

open NearCubicWires NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.WordPrograms
open StagePullback StagePullback.NativeRows

/-- `imp:pullback` and `lem:print`, paper/paper.tex: every actual native signed field fits its literal output
width, including all affine target shifts and the sign bit. -/
theorem nativeSource_fits (r : RowRequest) : StagePrint.NativeWidth.SourceFits r := by
  intro z hz
  rw [← signedRow_fields] at hz
  have hw : ∀ i, (r.child.weight i).natAbs ≤ 2^r.Lin :=
    fun i => (natAbs_le_encS _).trans (r.weightsFit i).le
  have ht : r.child.target.natAbs ≤ 2^r.Lin :=
    (natAbs_le_encS _).trans r.targetFits.le
  have hp : (targetPrefix r.point r.child r.parameters.n).natAbs ≤ r.parameters.n * 2^r.Lin :=
    (targetPrefix_abs_le_mass _ _ _).trans (massPrefix_le _ _ _ _ le_rfl r.weightsFit)
  apply sourceSlack r.parameters.n r.Lin z
  unfold signedRow at hz
  rcases List.mem_append.mp hz with hrow | htarget
  · have hroute := route_pad_abs r.child (sideList r.point r.transpose)
      (flipList r.point) (PrimT.C4Geo.width r.parameters) (2^r.Lin) hw z hrow
    calc
      _ ≤ 2^r.Lin := hroute
      _ ≤ (r.parameters.n + 1) * 2^r.Lin := by
        exact Nat.le_mul_of_pos_left _ (by omega)
  · have he := List.mem_singleton.mp htarget
    subst z
    rw [← targetPrefix_flipSum r.point r.child r.transpose]
    have hsub := Int.natAbs_add_le r.child.target (-targetPrefix r.point r.child r.parameters.n)
    rw [Int.natAbs_neg] at hsub
    calc
      _ ≤ r.child.target.natAbs + (targetPrefix r.point r.child r.parameters.n).natAbs := hsub
      _ ≤ 2^r.Lin + r.parameters.n * 2^r.Lin := Nat.add_le_add ht hp
      _ = _ := by ring

/-- `imp:pullback` and `lem:print`, paper/paper.tex: every actual seventeen-role original-child pool has the
common native source width already carried by the physical header. -/
theorem kids_fit (r : StageTuple.RowContext) : StagePrint.NativeWidth.KidsFit r := by
  intro i row hrow z hz
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hrow
  have hf := nativeSource_fits (r.originalRow i j).canonicalPullback z hz
  rw [r.originalRow_Lout_eq] at hf
  exact hf

end NearQuarticWires.StageNativeWidth
