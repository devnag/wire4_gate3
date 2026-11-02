import Proof.Quartic.StageLift.SourceEnvelope
import Proof.Quartic.StageLift.SourceCarrier
import Proof.Quartic.StageMain.CompactBounds
import Proof.Quartic.StageMain.HeaderWidth

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open Cells.ParameterArithmetic

/-- `prop:time`, paper/paper.tex: the source
workspace exponent depends only on the two fixed admission exponents. -/
def sourceWidthExponent (B1 B2 : ℕ) : ℕ :=
  StageMain.Compact.capacityExponent B1 B2 + B1 + 12

/-- `prop:time`, paper/paper.tex: one fixed
coefficient covers the selected scalar envelope and cached preparation. -/
def sourceWidthCoefficient (B1 : ℕ) : ℕ :=
  preparationCoefficient B1 + StageMain.Compact.capacityCoefficient B1 + 2

/-- `prop:time`, paper/paper.tex: the complete
source envelope is polynomial in original arity, uniformly over the
Gamma table and arbitrary raw digit and residue integers. -/
theorem sourceEnvelope_polynomial {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    sourceEnvelope r ≤ sourceWidthCoefficient B1 *
      (r.child.call.n + 1) ^ sourceWidthExponent B1 B2 := by
  have hp := StageMain.Compact.compactInput_length_arity r.child.dispatched r.child.witness
  change (preparedWordOf r).length ≤ _ at hp
  have hbase : 1 ≤ r.child.call.n + 1 := by omega
  have hP := Nat.mul_le_mul_left (StageMain.Compact.capacityCoefficient B1)
    (Nat.pow_le_pow_right hbase (show StageMain.Compact.capacityExponent B1 B2 ≤
      sourceWidthExponent B1 B2 by unfold sourceWidthExponent; omega))
  have hV := Nat.mul_le_mul_left (preparationCoefficient B1)
    (Nat.pow_le_pow_right hbase (show B1 + 12 ≤ sourceWidthExponent B1 B2 by
      unfold sourceWidthExponent; omega))
  have hpos : 1 ≤ (r.child.call.n + 1) ^ sourceWidthExponent B1 B2 := Nat.pow_pos hbase
  dsimp [sourceEnvelope, sourceWidthCoefficient, preparationEnvelope]
  nlinarith only [hp, hP, hV, hpos]

/-- Step 3 and `prop:time`, paper/paper.tex: allocation reads only the original tagged arity header;
no large source suffix contributes to the arithmetic width. -/
theorem printInput_header_width {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2)
    (suffix : List Bool) :
    leadOnes (Greedy.printInput r ++ suffix) = 1 + natBitLength r.child.call.n := by
  rw [printInput_preparedPrefix]
  simp only [preparedPrefixWord, List.cons_append, List.append_assoc]
  exact StageMain.taggedCall_header_width _ _

/-- `prop:time`, paper/paper.tex: a fixed
header-based arithmetic allocation supplies the full actual-source
workspace bound, including the residue body and measured prefix. -/
theorem source_arithmetic_width {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2)
    (suffix : List Bool) :
    100 * (sourceEnvelope r + 1) ^ 2 ≤
      2 ^ ((2 * sourceWidthExponent B1 B2) * leadOnes (Greedy.printInput r ++ suffix)) *
        (100 * (sourceWidthCoefficient B1 + 1) ^ 2) := by
  have hn : r.child.call.n + 1 ≤ 2 ^ (1 + natBitLength r.child.call.n) := by
    have h := lt_natBitLength r.child.call.n
    have hm := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ))
      (show natBitLength r.child.call.n ≤ 1 + natBitLength r.child.call.n by omega)
    omega
  have hpow := Nat.pow_le_pow_left hn (sourceWidthExponent B1 B2)
  rw [← pow_mul] at hpow
  have hpos : 1 ≤ 2 ^ ((1 + natBitLength r.child.call.n) * sourceWidthExponent B1 B2) :=
    Nat.pow_pos (by decide)
  have he := (sourceEnvelope_polynomial r).trans
    (Nat.mul_le_mul_left (sourceWidthCoefficient B1) hpow)
  have he1 : sourceEnvelope r + 1 ≤ (sourceWidthCoefficient B1 + 1) *
      2 ^ ((1 + natBitLength r.child.call.n) * sourceWidthExponent B1 B2) := by
    nlinarith only [he, hpos]
  have hh := Nat.mul_le_mul_left 100 (Nat.pow_le_pow_left he1 2)
  rw [printInput_header_width]
  calc
    _ ≤ 100 * ((sourceWidthCoefficient B1 + 1) *
        2 ^ ((1 + natBitLength r.child.call.n) * sourceWidthExponent B1 B2)) ^ 2 := hh
    _ = _ := by
      rw [mul_pow, ← pow_mul,
        show ((1 + natBitLength r.child.call.n) * sourceWidthExponent B1 B2) * 2 =
          (2 * sourceWidthExponent B1 B2) * (1 + natBitLength r.child.call.n) by ring]
      ac_rfl

end NearQuarticWires.StageLift
