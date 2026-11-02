import Proof.Quartic.StageHamming.Bounds
import Proof.MachineModel.OrdinaryBoundedCounter

set_option autoImplicit false

namespace NearQuarticWires.StageColumns

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicGates.Close.Cells

/-- `imp:partition` and `imp:pullback`, paper/paper.tex: the canonical generator is determined by these
four physically serialized scalar parameters. -/
def columnInput (P : StarParams) : List Bool :=
  natWord P.n ++ natWord P.r ++ natWord P.b ++ natWord P.s

def fields (P : StarParams) : List ℕ := [P.n, P.r, P.b, P.s]

/-- `imp:partition`, paper/paper.tex: the complete
source request has exactly four natural fields in the stated order. -/
theorem fields_word (P : StarParams) : (fields P).flatMap natWord = columnInput P := by
  simp [fields, columnInput, List.append_assoc]

/-- `imp:partition`, paper/paper.tex: every canonical
source parameter is bounded by the original input arity. -/
theorem fields_le (P : StarParams) (v : ℕ) (hv : v ∈ fields P) : v ≤ P.n := by
  have hr := P.four_r_le_n
  obtain ⟨hb, hs, _⟩ := StageHamming.block_dimensions_le P
  simp only [fields, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl <;> omega

/-- `imp:partition` and `lem:print`, paper/paper.tex: both generator dimensions are bounded by original arity. -/
theorem dimensions_le (P : StarParams) :
    PrimT.C4Geo.width P ≤ P.n ∧ PrimT.C4Geo.dRow P ≤ P.n := by
  have hb := P.r_mul_b_le
  have hh := Nat.mul_le_mul_right P.b (Nat.div_le_self P.r 2)
  have hf : (P.n - P.r * P.b + 1) / 2 ≤ P.n - P.r * P.b := by omega
  have hd := P.centerBits_sum
  constructor
  · unfold PrimT.C4Geo.width PrimT.C4Geo.hL
    omega
  · change P.leftCenterBits ≤ P.n
    omega

/-- `lem:print`, paper/paper.tex: a fixed-width
column word is exactly its original low-first bit sequence. -/
theorem binary_bitsValue (bits : List Bool) :
    SignedSortKey.binary bits.length (CanonicalBinary.bitsValue bits) = bits := by
  have hv : RadixSemantics.value bits = CanonicalBinary.bitsValue bits := by
    induction bits with
    | nil => rfl
    | cons b bs ih => simp only [RadixSemantics.value, CanonicalBinary.bitsValue, ih]
  simpa only [hv] using BoundedCounter.binary_of_value bits

/-- `imp:partition` and `lem:print`, paper/paper.tex: the column stream is produced in increasing basis order,
with one literal fixed-width frame per column. -/
def columnStream (P : StarParams) : List Bool :=
  (List.range (PrimT.C4Geo.dRow P)).flatMap fun j => frame (PrimT.C4Geo.colBits P j)

/-- `lem:print`, paper/paper.tex: emitting the
canonical bits directly gives the exact native generator-column codec. -/
theorem columnStream_eq (P : StarParams) : columnStream P =
    MatrixScorePhi.columnsWord (PrimT.C4Geo.width P) (PrimT.C4Geo.cols P) := by
  unfold columnStream MatrixScorePhi.columnsWord PrimT.C4Geo.cols
  simp only [List.flatMap_map]
  apply congrArg (fun f : ℕ → List Bool => (List.range (PrimT.C4Geo.dRow P)).flatMap f)
  funext j
  apply congrArg frame
  have hb : SignedSortKey.binary (PrimT.C4Geo.width P)
      (CanonicalBinary.bitsValue (PrimT.C4Geo.colBits P j)) = PrimT.C4Geo.colBits P j := by
    simpa only [PrimT.C4Geo.colBits, List.length_ofFn] using
      binary_bitsValue (PrimT.C4Geo.colBits P j)
  exact hb.symm

/-- `lem:print`, paper/paper.tex: the native
column field has one outer frame, enclosing its natural width and
the exact stream of individually framed column bits. -/
theorem colsField_stream (P : StarParams) : PrimT.C4Geo.colsField P =
    frame (natWord (PrimT.C4Geo.width P) ++ columnStream P) := by
  rw [columnStream_eq]
  rfl

/-- `prop:time`, paper/paper.tex: the actual
data-position and parity scans have one uniform quadratic scalar clock. -/
def bitClock (P : StarParams) : ℕ :=
  P.b * (8 * P.s + 24) + P.s * (5 * P.s + 21) + 200

/-- `prop:time`, paper/paper.tex: scalar column
computation is bounded by a fixed quadratic in the original dimension. -/
theorem bitClock_le (P : StarParams) : bitClock P ≤ 100 * (P.n + 2) ^ 2 := by
  obtain ⟨hb, hs, _⟩ := StageHamming.block_dimensions_le P
  have hsn : P.s ≤ P.n := hs.trans hb
  calc
    bitClock P ≤ P.n * (8 * P.n + 24) + P.n * (5 * P.n + 21) + 200 := by
      unfold bitClock
      gcongr
    _ ≤ _ := by nlinarith

end NearQuarticWires.StageColumns
