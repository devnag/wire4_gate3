import Proof.Quartic.StageLift.ReduceFormula
import Proof.Gates.Cells.InputLen

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats

/-- `lem:print`, paper/paper.tex: binary payload
length increases monotonically with its actual nonnegative value. -/
theorem codec_nbl_mono {a b : ℕ} (h : a ≤ b) : natBitLength a ≤ natBitLength b := by
  unfold natBitLength
  have := Nat.log_mono_right (b := 2) h
  omega

/-- `lem:print`, paper/paper.tex: the literal
constant-token length includes its natural tag, natural sign and magnitude. -/
theorem constant_token_bytes (z : ℤ) :
    (tokWord (.const z)).length = 2 * natBitLength z.natAbs + 7 := by
  have hzero : (natWord 0).length = 3 := by decide
  have hsign : (natWord (if z < 0 then 1 else 0)).length = 3 := by
    split <;> decide
  simp only [tokWord, NearCubicGates.Close.Interfaces.intWord, List.length_append,
    hzero, hsign, NearCubicGates.Close.Cells.natWord_length]
  omega

/-- `lem:print` and `lem:residue`, paper/paper.tex: a reduced constant's actual magnitude fits the binary
length of q, independently of the original signed index value. -/
theorem reduced_constant_bits (q : ℕ) (hq : 0 < q) (z : ℤ) :
    natBitLength (z % (q : ℤ)).natAbs ≤ natBitLength q := by
  have hz0 : 0 ≤ z % (q : ℤ) := Int.emod_nonneg _ (by exact_mod_cast ne_of_gt hq)
  have hzq : z % (q : ℤ) < q := Int.emod_lt_of_pos _ (by exact_mod_cast hq)
  apply codec_nbl_mono
  have hcast : ((z % (q : ℤ)).natAbs : ℤ) = z % (q : ℤ) := by
    rw [Int.natCast_natAbs, abs_of_nonneg hz0]
  exact_mod_cast (show ((z % (q : ℤ)).natAbs : ℤ) ≤ q by rw [hcast]; omega)

/-- `lem:print`, paper/paper.tex: the actual
postfix bytes of a Formula are the concatenated original token codec. -/
def formulaTokenBytes {V : ℕ} (F : Formula V) : ℕ :=
  ((toks F).flatMap tokWord).length

/-- `lem:print`, paper/paper.tex: a per-syntax-node
byte factor depends only on the atom and actual modulus bit lengths. -/
def formulaByteFactor (V q : ℕ) : ℕ :=
  2 * (natBitLength V + natBitLength q) + 15

/-- `lem:print`, paper/paper.tex: reducing every
constant before token emission bounds the literal bytes by syntactic
size times atom/modulus bit lengths, never by raw Formula values. -/
theorem reduced_formula_token_bytes {V : ℕ} (q : ℕ) (hq : 0 < q) (F : Formula V) :
    formulaTokenBytes (reduceConstants q F) ≤ formulaByteFactor V q * F.size := by
  have hK : 15 ≤ formulaByteFactor V q := by unfold formulaByteFactor; omega
  induction F with
  | const z =>
      have hb := reduced_constant_bits q hq z
      simp only [formulaTokenBytes, reduceConstants, toks, List.flatMap_singleton,
        constant_token_bytes, Formula.size, Nat.mul_one]
      unfold formulaByteFactor
      omega
  | var atom =>
      have hb := codec_nbl_mono atom.isLt.le
      have ht : (natWord 1).length = 3 := by decide
      simp only [formulaTokenBytes, reduceConstants, toks, List.flatMap_singleton,
        tokWord, List.length_append, ht, NearCubicGates.Close.Cells.natWord_length,
        Formula.size, Nat.mul_one]
      unfold formulaByteFactor
      omega
  | add left right ihl ihr =>
      have ht : (tokWord .add).length = 5 := by decide
      simp only [formulaTokenBytes, reduceConstants, toks, List.flatMap_append,
        List.flatMap_singleton, List.length_append, ht, Formula.size]
      dsimp only [formulaTokenBytes] at ihl ihr
      nlinarith
  | sub left right ihl ihr =>
      have ht : (tokWord .sub).length = 7 := by decide
      simp only [formulaTokenBytes, reduceConstants, toks, List.flatMap_append,
        List.flatMap_singleton, List.length_append, ht, Formula.size]
      dsimp only [formulaTokenBytes] at ihl ihr
      nlinarith
  | mul left right ihl ihr =>
      have ht : (tokWord .mul).length = 7 := by decide
      simp only [formulaTokenBytes, reduceConstants, toks, List.flatMap_append,
        List.flatMap_singleton, List.length_append, ht, Formula.size]
      dsimp only [formulaTokenBytes] at ihl ihr
      nlinarith
  | neg child ih =>
      have ht : (tokWord .neg).length = 5 := by decide
      simp only [formulaTokenBytes, reduceConstants, toks, List.flatMap_append,
        List.flatMap_singleton, List.length_append, ht, Formula.size]
      dsimp only [formulaTokenBytes] at ih
      nlinarith
  | pow child exponent ih =>
      have he := NearCubicGates.Close.Cells.nbl_le_self exponent
      have ht : (natWord 6).length = 7 := by decide
      have hm := Nat.mul_le_mul_right (exponent + 1) hK
      simp only [formulaTokenBytes, reduceConstants, toks, List.flatMap_append,
        List.flatMap_singleton, List.length_append, tokWord, ht,
        NearCubicGates.Close.Cells.natWord_length, Formula.size]
      dsimp only [formulaTokenBytes] at ih
      nlinarith

/-- `lem:print`, paper/paper.tex: the postfix
token count is bounded by unary-exponent syntax size. -/
theorem formula_tokens_le_size {V : ℕ} (F : Formula V) : (toks F).length ≤ F.size := by
  induction F <;> simp_all [toks, Formula.size] <;> omega

/-- `lem:print`, paper/paper.tex: the complete
canonical Formula codec includes paid arity and token-count headers,
both bounded without a raw coefficient or expanded-polynomial premise. -/
theorem reduced_formula_word_bytes {V : ℕ} (q : ℕ) (hq : 0 < q) (F : Formula V) :
    (formulaWord ⟨V, reduceConstants q F⟩).length ≤
      (formulaByteFactor V q + 2) * F.size + 2 * natBitLength V + 4 := by
  have hL := reduced_formula_token_bytes q hq F
  have hN := formula_tokens_le_size F
  have hn := NearCubicGates.Close.Cells.nbl_le_self (toks F).length
  simp only [formulaWord, NearCubicGates.Close.Interfaces.listWord, List.length_append,
    reduceConstants_token_count, NearCubicGates.Close.Cells.natWord_length]
  dsimp only [formulaTokenBytes] at hL
  nlinarith

end NearQuarticWires.StageLift
