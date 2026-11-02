import Proof.Quartic.StageLift.SourceGuards
import Proof.Quartic.StageLift.FormulaBytes

/-!
# Finite arithmetic space for the residue source

`lem:residue`, `imp:amp` and `prop:time`, paper/paper.tex: normalized residues, digit
coefficients, indices and exact binomial intermediates fit the stated
binary workspace. The envelope is a proof bound, not an input field.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageLiftTokens
open NearCubicWires
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open StageLift

def sourceBits (E : ℕ) : ℕ := 10*(E+1)^2

theorem source_small_capacity (E W : ℕ) (hE : 2≤E) (hW : 100*(E+1)^2≤W) :
    20*(E+1)^3<2^W := by
  have hbase : E+1≤2^E := Nat.lt_two_pow_self
  have hexp : 5+E*3<W := by nlinarith
  calc
    20*(E+1)^3≤2^5*(2^E)^3 := Nat.mul_le_mul (by decide) (Nat.pow_le_pow_left hbase _)
    _ = 2^(5+E*3) := by rw [pow_add,pow_mul]
    _ < 2^W := Nat.pow_lt_pow_right (by decide) hexp

theorem source_width (E W : ℕ) (hE : 2≤E) (hW : 100*(E+1)^2≤W) : 5≤W := by
  nlinarith

theorem source_bits_capacity (E W : ℕ) (hE : 2≤E) (hW : 100*(E+1)^2≤W) :
    sourceBits E+2<2^W := by
  apply lt_of_le_of_lt _ (source_small_capacity E W hE hW)
  unfold sourceBits
  nlinarith [Nat.mul_self_le_mul_self (show 1≤E+1 by omega)]

theorem source_count_capacity (E W v : ℕ) (hE : 2≤E) (hW : 100*(E+1)^2≤W)
    (hv : v≤20*(E+1)^3) : v<2^W :=
  lt_of_le_of_lt hv (source_small_capacity E W hE hW)

theorem source_small_bits (E v : ℕ) (hE : 2≤E) (hv : v≤20*(E+1)^3) :
    natBitLength v≤ sourceBits E := by
  have hbase : E+1≤2^E := Nat.lt_two_pow_self
  apply nbl_le_of_lt _ (by unfold sourceBits; nlinarith)
  calc
    v≤20*(E+1)^3 := hv
    _ ≤2^5*(2^E)^3 := Nat.mul_le_mul (by decide) (Nat.pow_le_pow_left hbase _)
    _ =2^(5+E*3) := by rw [pow_add,pow_mul]
    _ <2^(sourceBits E) := Nat.pow_lt_pow_right (by decide) (by unfold sourceBits; nlinarith)

theorem source_modulus_bound (E p e : ℕ) (hp : p≤E) (he : e≤E) :
    p^e≤2^(E*E) := by
  have hb : p≤2^E := hp.trans Nat.lt_two_pow_self.le
  calc
    p^e≤(2^E)^e := Nat.pow_le_pow_left hb _
    _ =2^(E*e) := (pow_mul _ _ _).symm
    _ ≤2^(E*E) := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ he)

theorem source_modulus_bits (E p e : ℕ) (hE : 2≤E) (hp : p≤E) (he : e≤E) :
    natBitLength (p^e)≤ sourceBits E := by
  apply nbl_le_of_lt _ (by unfold sourceBits; nlinarith)
  exact lt_of_le_of_lt (source_modulus_bound E p e hp he)
    (Nat.pow_lt_pow_right (by decide) (by unfold sourceBits; nlinarith))

theorem source_binomial_capacity (E W e : ℕ) (hE : 2≤E)
    (hW : 100*(E+1)^2≤W) (he : e≤E) : 2^(2*e)*(2*e+1)<2^W := by
  have hb : 2*e+1≤2^(2*e) := Nat.lt_two_pow_self
  calc
    2^(2*e)*(2*e+1)≤2^(2*e)*2^(2*e) := Nat.mul_le_mul_left _ hb
    _ =2^(4*e) := by rw [←pow_add]; congr 1; omega
    _ <2^W := Nat.pow_lt_pow_right (by decide) (by nlinarith)

theorem source_binomial_bits (E e j : ℕ) (hE : 2≤E) (he : e≤E) (hj : j<e) :
    natBitLength ((e-1+j).choose j)≤ sourceBits E := by
  have hb := Nat.choose_le_two_pow (e-1+j) j
  apply nbl_le_of_lt _ (by unfold sourceBits; nlinarith)
  exact lt_of_le_of_lt hb (Nat.pow_lt_pow_right (by decide)
    (by unfold sourceBits; have hsub := Nat.sub_le e 1; nlinarith))

end NearQuarticWires.StageLiftTokens
