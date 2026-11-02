import Proof.Quartic.StagePrint.BaseHeaderEmit
import Proof.Quartic.StageLift.FrameLoop
import Proof.Quartic.StageLift.MemorySource
import Proof.Quartic.StageRecovery.OutputFrame
import Proof.Gates.CounterMachine.PrefixRun

set_option autoImplicit false

namespace NearQuarticWires.StageNativeRowCount

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5
open NearCubicGates.Close.Cells

/-- `imp:pullback` and `lem:print`, paper/paper.tex: only the existing actual retained affine header is input. -/
structure Request where
  header : StagePrint.Header.HeaderCall

def Request.payload (r : Request) : List Bool :=
  (StagePrint.Header.baseHeaderValues r.header).flatMap natWord

def Request.word (r : Request) : List Bool := frame r.payload

/-- `imp:pullback`, paper/paper.tex: this is the
number of signed native row fields, distinct from their bit width. -/
def Request.rowFieldCount (r : Request) : ℕ :=
  2 * PrimT.C4Geo.width r.header.prepared.starParams + 1

def Request.output (r : Request) : List Bool := frame (natWord r.rowFieldCount)

def countValue (n r b : ℕ) : ℕ := 2 * ((r / 2) * b + (n - r * b + 1) / 2) + 1

/-- `imp:pullback`, paper/paper.tex: the exact
selected star projections give the literal natural-subtraction formula. -/
theorem Request.count_eq (r : Request) : r.rowFieldCount =
    countValue r.header.call.n r.header.parameters.r r.header.parameters.b := by
  unfold Request.rowFieldCount countValue PrimT.C4Geo.width PrimT.C4Geo.hL
  rw [r.header.prepared.star_b]
  rfl

theorem Request.geometry_bounds (r : Request) :
    r.header.parameters.r * r.header.parameters.b ≤ r.header.call.n ∧
      r.header.parameters.r ≤ r.header.call.n ∧ r.header.parameters.b ≤ r.header.call.n := by
  let P := r.header.prepared.starParams
  have hrb := P.r_mul_b_le
  rw [r.header.prepared.star_b] at hrb
  have hr := P.four_r_le_n
  have hb := (Nat.le_mul_of_pos_left P.b P.r_pos).trans P.r_mul_b_le
  rw [r.header.prepared.star_b] at hb
  exact ⟨hrb, by change 4 * r.header.parameters.r ≤ r.header.call.n at hr; omega, hb⟩

theorem countValue_le (n r b : ℕ) (hrb : r * b ≤ n) : countValue n r b ≤ 4 * n + 3 := by
  have hh := Nat.mul_le_mul_right b (Nat.div_le_self r 2)
  have hl := Nat.div_le_self (n - r * b + 1) 2
  unfold countValue
  omega

theorem Request.count_bound (r : Request) : r.rowFieldCount ≤ 4 * r.header.call.n + 3 := by
  rw [r.count_eq]
  exact countValue_le _ _ _ r.geometry_bounds.1

def headerStore : Fin MM := 0

def nReg : Fin VV := 20
def rReg : Fin VV := 21
def bReg : Fin VV := 22
def halfReg : Fin VV := 23
def blockReg : Fin VV := 24
def countReg : Fin VV := 25

end NearQuarticWires.StageNativeRowCount
