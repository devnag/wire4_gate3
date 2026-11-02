import Proof.Quartic.StagePullback.RowLoop
import Proof.Quartic.StagePullback.RowsOutput
import Proof.Gates.TabMachine.CompileM

set_option autoImplicit false

namespace NearQuarticWires.StagePullback

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.CounterMachine.CellTablesProg

/-- `imp:pullback` and `lem:print`, paper/paper.tex: one original signed child row and the actual canonical
star metadata determining its affine native pullback. -/
structure RowRequest where
  parameters : StarParams
  translation : parameters.Translation
  left : Fin (2 ^ SeedFix.callKh parameters)
  right : Fin (2 ^ SeedFix.callKh parameters)
  useLeft : Bool
  useRight : Bool
  transpose : Bool
  Lin : ℕ
  Lin_pos : 1 ≤ Lin
  Lin_le : Lin ≤ 4 * (parameters.n + 1) ^ 2 + 5
  child : ExactThresholdGate parameters.n
  weightsFit : ∀ i, SInt.encS (child.weight i) < 2 ^ Lin
  targetFits : SInt.encS child.target < 2 ^ Lin

/-- `imp:pullback`, paper/paper.tex: a common signed
output width covers the original target and all affine weight shifts. -/
def RowRequest.Lout (r : RowRequest) : ℕ := r.Lin + r.parameters.n + 6

/-- `imp:pullback`, paper/paper.tex: canonical affine
metadata do not depend on any particular row or column center code. -/
def RowRequest.point (r : RowRequest) : PointRequest where
  parameters := r.parameters
  translation := r.translation
  row := ⟨0, Nat.two_pow_pos _⟩
  column := ⟨0, Nat.two_pow_pos _⟩
  left := r.left
  right := r.right
  useLeft := r.useLeft
  useRight := r.useRight

/-- `imp:pullback` and `lem:print`, paper/paper.tex: exact scalar fields of the original signed-row request. -/
def RowRequest.fields (r : RowRequest) : List ℕ :=
  [r.parameters.n, r.Lin, r.Lout, r.parameters.r, r.parameters.b, r.parameters.s,
    translationNumber r.parameters r.translation, r.left.val, r.right.val]

def RowRequest.body (r : RowRequest) : List Bool :=
  (List.ofFn r.child.weight ++ [r.child.target]).flatMap (fun z =>
    SignedSortKey.binary r.Lin (SInt.encS z))

def RowRequest.word (r : RowRequest) : List Bool :=
  r.fields.flatMap natWord ++ [r.useLeft, r.useRight, r.transpose] ++ r.body

/-- `imp:pullback` and `lem:print`, paper/paper.tex: the exact dense signed output encodings in native left,
native right and affine-target order. -/
def RowRequest.numbers (r : RowRequest) : List ℕ :=
  NativeRows.padNumbers (PrimT.C4Geo.width r.parameters)
      (NativeRows.rowNumbers r.point r.child r.transpose true r.parameters.n) ++
    NativeRows.padNumbers (PrimT.C4Geo.width r.parameters)
      (NativeRows.rowNumbers r.point r.child r.transpose false r.parameters.n) ++
    [SInt.encS (r.child.target - NativeRows.targetPrefix r.point r.child r.parameters.n)]

def RowRequest.output (r : RowRequest) : List Bool :=
  r.numbers.flatMap (fun v => frame (SignedSortKey.binary r.Lout v))

/-- `lem:print`, paper/paper.tex: the row input is
the original compiler's exact unframed fixed signed record body. -/
theorem RowRequest.body_recBits (r : RowRequest) :
    r.body = NearCubicGates.Close.TabMachine.recBits (r.Lin - 1)
      (List.ofFn r.child.weight ++ [r.child.target]) := by
  unfold RowRequest.body NearCubicGates.Close.TabMachine.recBits
  rw [Nat.sub_add_cancel r.Lin_pos]

/-- `imp:pullback`, paper/paper.tex: there are exactly
nine explicit scalar fields before the physical flags and original row. -/
theorem RowRequest.fields_length (r : RowRequest) : r.fields.length = 9 := rfl

/-- `prop:time`, paper/paper.tex: original signed
row fields and canonical metadata fit the common physical parser width. -/
theorem RowRequest.fields_lt (r : RowRequest) (v : ℕ) (hv : v ∈ r.fields) :
    v < 2 ^ (r.Lout + 1) := by
  have hn : r.parameters.n + 1 ≤ r.Lout + 1 := by unfold RowRequest.Lout; omega
  have hg (v : ℕ) (hv : v ∈ r.point.fields) : v < 2 ^ (r.Lout + 1) :=
    (r.point.fields_lt v hv).trans_le (Nat.pow_le_pow_right (by decide) hn)
  have hL : r.Lout < 2 ^ (r.Lout + 1) :=
    (Nat.lt_two_pow_self (n := r.Lout)).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  simp only [RowRequest.fields, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hg _ (by simp [PointRequest.fields, RowRequest.point])
  · exact (show r.Lin ≤ r.Lout by unfold RowRequest.Lout; omega).trans_lt hL
  · exact hL
  · exact hg _ (by simp [PointRequest.fields, RowRequest.point])
  · exact hg _ (by simp [PointRequest.fields, RowRequest.point])
  · exact hg _ (by simp [PointRequest.fields, RowRequest.point])
  · exact hg _ (by simp [PointRequest.fields, RowRequest.point])
  · exact hg _ (by simp [PointRequest.fields, RowRequest.point])
  · exact hg _ (by simp [PointRequest.fields, RowRequest.point])

/-- `prop:time`, paper/paper.tex: the complete
original scalar header has bounded actual binary field lengths. -/
theorem RowRequest.fields_bitLength (r : RowRequest) (v : ℕ) (hv : v ∈ r.fields) :
    natBitLength v ≤ r.Lout + 1 :=
  natBitLength_le_of_lt v _ (by omega) (r.fields_lt v hv)

end NearQuarticWires.StagePullback
