import Proof.Quartic.StageOutput.ArithmeticCore
import Proof.Quartic.StageOutput.PaddedBounds
import Proof.Quartic.StageOutput.Capacity
import Proof.Quartic.StageOutput.Validity

/-!
# Reading and answering the scalar branch of Step 5

Paper: `sec:algorithm`, paper/paper.tex. The thirteen
encoded fields are read in order. An inconsistent seed path prints the
sound default; a consistent path executes the exact endpoint arithmetic
and prints its two rational outputs. Trailing allocation bits are inert.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageOutput

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Dispatch NearCubicGates.Close.Interfaces

def trueOutputBody : St VV := .seq parseInput
  (.ite (.eq 28 v1) arithmeticCore (emitL (outputWord Algorithm.soundDefault)))

theorem trueOutputBody_spec {C : Ctx} (d : Input) (ha : d.Admissible)
    (hW : 64 * (d.padded.length + 1) ≤ C.Wd)
    (hL : C.cw.length + 2 < 2 ^ C.Wd)
    (a : DS VV) (hc : Cst a) (hv : Valid C a) (rest : List Bool)
    (hin : C.cw.drop a.cp = d.word ++ rest) :
    Hs C trueOutputBody a (2000 * C.Wd + 2000) (fun b =>
      b.out = a.out ++ outputWord d.result) := by
  have hn : d.n ≤ d.padded.length := by rw [d.padded_length]; omega
  have hk : d.k ≤ d.padded.length := ha.k_le_n.trans hn
  have hword : d.word.length ≤ C.Wd := by rw [d.padded_length] at hW; omega
  have hvals : ∀ xv ∈ d.fields, natBitLength xv.2 + 2 ≤ C.Wd := by
    intro xv hx
    have hh := fieldWord_length d.fields xv hx
    rw [natWord_length] at hh
    change 2 * natBitLength xv.2 + 1 ≤ d.word.length at hh
    have := natBitLength_pos xv.2
    rw [d.padded_length] at hW
    omega
  have hcapacity := arithmetic_capacity d d.padded.length C.Wd d.field_capacity hn hk hW
  refine Hx.hs (Hs.then (Hs.addValid (by omega) hv (parseInput_spec d hvals hL a hc rest hin))
    (fun b ⟨⟨bs, _, _, bo, bc, _⟩, bv⟩ n1 hn1 => ?_))
  have bflag : b.env 28 = d.consistent.toNat := bs.2.2.2.2.2.2.2.2.1
  cases hcon : d.consistent with
  | false =>
    have he : (Cnd.eq 28 v1).eval b = false := by simp [Cnd.eval, bflag, hcon, bc.one]
    refine Hs.last (Hs.iteF (show (28 : Fin VV) ≠ v1 from by decide) he
      (emitL_spec (C := C) (outputWord Algorithm.soundDefault) b)) ?_
    rintro e ⟨eo, _⟩ n2 hn2
    refine ⟨?_, ?_⟩
    · simpa only [Input.result, hcon, Bool.false_eq_true, ↓reduceIte, bo] using eo
    · have hcst := readScalarsCost_le_word d.fields
      change readScalarsCost d.fields ≤ 40 * d.word.length + 1 at hcst
      norm_num [outputWord, ratWord, NearCubicGates.Close.Interfaces.intWord,
        Algorithm.soundDefault, natWord, natBitLength] at hn2
      omega
  | true =>
    have he : (Cnd.eq 28 v1).eval b = true := by simp [Cnd.eval, bflag, hcon, bc.one]
    refine Hs.last (Hs.iteT (show (28 : Fin VV) ≠ v1 from by decide) he
      (arithmeticCore_spec d d.padded.length (2 ^ (28 * (d.padded.length + 1) + 2))
        b bc bv bs d.field_capacity hn hk hW ha.denominator_pos ha.ceil_nonneg
        ha.center_nonneg ha.radius_nonneg hcapacity.1 hcapacity.2.1 hcapacity.2.2.1
        hcapacity.2.2.2.1 hcapacity.2.2.2.2)) ?_
    rintro e ⟨eo, _⟩ n2 hn2
    refine ⟨?_, ?_⟩
    · simpa only [Input.result, hcon, ↓reduceIte, bo] using eo
    · have hcst := readScalarsCost_le_word d.fields
      change readScalarsCost d.fields ≤ 40 * d.word.length + 1 at hcst
      omega

end NearQuarticWires.StageOutput
