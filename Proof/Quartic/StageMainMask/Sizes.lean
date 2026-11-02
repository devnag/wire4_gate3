import Proof.Quartic.StageMainMask.Capacity
import Proof.Quartic.StageMain.RuntimeSizes

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open StageMain StageMain.Compact StageLift

private theorem exists_entrySizePair (B1 B2 : ℕ) :
    ∃ p : ℕ × ℕ, ∀ r : EntryRequest B1 B2,
      entryResources r ≤ p.1 * (r.call.n + 1) ^ p.2 := by
  obtain ⟨K, d, h⟩ := entryResources_arity B1 B2
  exact ⟨(K, d), h⟩

/-- `prop:time`, paper/paper.tex: two fixed
natural constants bound every actual Entry resource for the chosen
input class, uniformly over witnesses, columns and samples. -/
noncomputable def entrySizePair (B1 B2 : ℕ) : ℕ × ℕ :=
  Classical.choose (exists_entrySizePair B1 B2)

/-- `prop:time`, paper/paper.tex: the fixed
resource constants are obtained from the proved complete original
source and actual cold-subroutine polynomial bound. -/
theorem entrySizePair_spec (B1 B2 : ℕ) (r : EntryRequest B1 B2) :
    entryResources r ≤ (entrySizePair B1 B2).1 * (r.call.n + 1) ^ (entrySizePair B1 B2).2 :=
  Classical.choose_spec (exists_entrySizePair B1 B2) r

/-- `prop:time`, paper/paper.tex: one fixed
arity-header reservation funds the native scalar width, the actual
ordinary input streams and the actual cold-helper call clocks. -/
noncomputable def entrySizes (B1 B2 : ℕ) : Sz :=
  let p := entrySizePair B1 B2
  ⟨p.1 + 64, p.2, p.1 + 64, p.2, p.1 + 64, p.2⟩

/-- `prop:time`, paper/paper.tex: the native
binary workspace includes its fixed constants on every source header. -/
theorem entrySizes_min (B1 B2 l : ℕ) : 64 ≤ (entrySizes B1 B2).W l := by
  have hp : 1 ≤ (2 : ℕ) ^ ((entrySizePair B1 B2).2 * l) := Nat.one_le_two_pow
  unfold entrySizes Sz.W
  nlinarith

/-- `prop:time`, paper/paper.tex: the actual
ordinary input and call-clock reservations equal the common funded
native scalar reservation, rather than separate unproved capacities. -/
theorem entrySizes_reserves (B1 B2 l : ℕ) :
    (entrySizes B1 B2).Lk l = (entrySizes B1 B2).W l ∧
      (entrySizes B1 B2).Bk l = (entrySizes B1 B2).W l := ⟨rfl, rfl⟩

/-- `prop:time`, paper/paper.tex: the original
numeric Entry word keeps the successful preparation tag and literal
original arity header; no long source suffix determines the width. -/
theorem entryWord_header {B1 B2 : ℕ} (r : EntryRequest B1 B2) :
    leadOnes (entryWord r) = 1 + natBitLength r.call.n := by
  rw [entryWord, prepWord_eq_compact r.dispatched]
  simp only [compactInput, preparedPrefixWord, List.cons_append, List.append_assoc]
  exact taggedCall_header_width r.call _

/-- `prop:time`, paper/paper.tex: the literal
original arity header physically supplies every actual Entry resource,
including the complete cold helper call reservations. -/
theorem entrySizes_resources {B1 B2 : ℕ} (r : EntryRequest B1 B2) :
    entryResources r ≤ (entrySizes B1 B2).W (leadOnes (entryWord r)) := by
  have hb := entrySizePair_spec B1 B2 r
  have hn : r.call.n + 1 ≤ 2 ^ (1 + natBitLength r.call.n) := by
    have hh := lt_natBitLength r.call.n
    have hp := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ))
      (show natBitLength r.call.n ≤ 1 + natBitLength r.call.n by omega)
    omega
  have hpow := Nat.pow_le_pow_left hn (entrySizePair B1 B2).2
  rw [entryWord_header]
  calc
    _ ≤ (entrySizePair B1 B2).1 * (r.call.n + 1) ^ (entrySizePair B1 B2).2 := hb
    _ ≤ ((2 ^ (1 + natBitLength r.call.n)) ^ (entrySizePair B1 B2).2) *
        ((entrySizePair B1 B2).1 + 64) := by
      calc
        _ ≤ (entrySizePair B1 B2).1 * (2 ^ (1 + natBitLength r.call.n)) ^ (entrySizePair B1 B2).2 :=
          Nat.mul_le_mul_left _ hpow
        _ ≤ _ := by
          rw [Nat.mul_comm (entrySizePair B1 B2).1]
          exact Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
    _ = _ := by
      unfold entrySizes Sz.W
      rw [← pow_mul, Nat.mul_comm (1 + natBitLength r.call.n)]

end NearQuarticWires.StageMainMask
