import Proof.Quartic.StageRecovery.FamilyRetained
import Proof.Quartic.StageRecovery.FamilyPacketLoad
import Proof.Quartic.StageRecovery.FamilyHeaderSuffix

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicWires NearCubicGates.Close.Cells NearCubicGates.Close.Expand
open NearCubicGates.Close.Interfaces.Formats

/-- `prop:time`, paper/paper.tex: the original actual
postfix bytes are bounded by the serialized structural Formula hint. -/
theorem FamilyCompileRequest.token_length_le (r : FamilyCompileRequest) :
    (tokenStream (toks r.source.formula)).length ≤ r.source.hint := by
  have hh := r.source.hint_sufficient
  have hs : r.source.arity + r.source.formula.size +
      (formulaWord ⟨r.source.arity, r.source.formula⟩).length + natBitLength r.source.modulus + 10 ≤
      r.source.hint := (Nat.le_self_pow (by norm_num) _).trans hh
  have ht : (tokenStream (toks r.source.formula)).length ≤
      (formulaWord ⟨r.source.arity, r.source.formula⟩).length := by
    simp only [formulaWord, NearCubicGates.Close.Interfaces.listWord, tokenStream, List.length_append]
    omega
  omega

/-- `prop:time`, paper/paper.tex: the actual generated
family has binary count height at most the product of degree and arity. -/
theorem FamilyCompileRequest.family_count_bound (r : FamilyCompileRequest) :
    (famRecs r.source.arity r.degree).length ≤ 2 ^ (r.source.arity * r.degree) := by
  rw [famRecs_length]
  calc (fam r.source.arity r.degree).length ≤ (r.source.arity + 1) ^ r.degree := fam_length_le _ _
    _ ≤ (2 ^ r.source.arity) ^ r.degree := Nat.pow_le_pow_left Nat.lt_two_pow_self _
    _ = _ := by rw [pow_mul]

/-- `prop:time`, paper/paper.tex: the small structural
hint covers every exponent needed by the one-time native packet return. -/
theorem FamilyCompileRequest.family_span_exponent (r : FamilyCompileRequest) :
    r.source.arity * r.degree + r.family.width + 2 ≤ r.setupHint := by
  dsimp [FamilyCompileRequest.family, FamilyRequest.width, FamilyCompileRequest.setupHint]
  nlinarith

/-- `lem:print`, paper/paper.tex: every actual native
record fits its declared original binary width before parsing. -/
theorem FamilyCompileRequest.family_records_fit (r : FamilyCompileRequest) :
    ∀ v ∈ famRecs r.source.arity r.degree, v < 2 ^ r.family.width := by
  intro v hv
  have h := famRecs_lt r.source.arity r.degree v hv
  have hfit := r.family.records_fit
  have hle : (r.degree + 1) * 2 ^ r.source.arity ≤ (r.degree + 3) * 2 ^ r.source.arity :=
    Nat.mul_le_mul_right _ (by omega)
  exact h.trans_le (hle.trans hfit.le)

/-- `prop:time`, paper/paper.tex: actual count and
packet-frame span fit the same small binary workspace used by caching. -/
theorem FamilyCompileRequest.family_parser_bounds (C : Ctx) (r : FamilyCompileRequest)
    (hwidth : 64 * (r.setupHint + 1) ≤ C.Wd) :
    r.family.width + 2 ≤ C.Wd ∧
      (famRecs r.source.arity r.degree).length < 2 ^ C.Wd ∧
      (tokenStream (toks r.source.formula)).length < 2 ^ C.Wd ∧
      2 * r.family.width + 1 < 2 ^ C.Wd ∧
      (tokenStream (toks r.source.formula)).length +
        (famRecs r.source.arity r.degree).length * (2 * r.family.width + 1) + 1 < 2 ^ C.Wd := by
  let V := r.source.arity
  let D := r.degree
  let W := r.family.width
  let H := r.setupHint
  let N := (famRecs V D).length
  let L := (tokenStream (toks r.source.formula)).length
  have hW := r.setupHint_width
  have he := r.family_span_exponent
  change W + 2 ≤ H at hW
  change V * D + W + 2 ≤ H at he
  change 64 * (H + 1) ≤ C.Wd at hwidth
  have hN : N ≤ 2 ^ (V * D) := r.family_count_bound
  have hLH : L ≤ H := by
    have hl := r.token_length_le
    dsimp [FamilyCompileRequest.setupHint, H]
    omega
  have hspan : 2 * W + 1 < 2 ^ (W + 1) := by
    have hh : W + 1 ≤ 2 ^ W := Nat.lt_two_pow_self
    have ht := Nat.mul_le_mul_left 2 hh
    rw [show 2 * 2 ^ W = 2 ^ (W + 1) by ring] at ht
    omega
  have hprod : N * (2 * W + 1) < 2 ^ H := by
    calc N * (2 * W + 1) ≤ 2 ^ (V * D) * (2 * W + 1) := Nat.mul_le_mul_right _ hN
      _ < 2 ^ (V * D) * 2 ^ (W + 1) := Nat.mul_lt_mul_of_pos_left hspan (by positivity)
      _ = 2 ^ (V * D + (W + 1)) := (pow_add (2 : ℕ) (V * D) (W + 1)).symm
      _ ≤ 2 ^ H := Nat.pow_le_pow_right (by decide) (by omega)
  have hreturn : L + N * (2 * W + 1) + 1 < 2 ^ (H + 1) := by
    have hH : H + 1 ≤ 2 ^ H := Nat.lt_two_pow_self
    have h2 : 2 ^ (H + 1) = 2 * 2 ^ H := by ring
    omega
  have hp : 2 ^ (H + 1) ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (by decide) (by omega)
  have hNsmall : N < 2 ^ C.Wd := by
    calc N ≤ 2 ^ (V * D) := hN
      _ < 2 ^ C.Wd := Nat.pow_lt_pow_right (by decide) (by omega)
  have hretfit : L + N * (2 * W + 1) + 1 < 2 ^ C.Wd := hreturn.trans_le hp
  exact ⟨by omega, hNsmall, by omega,
    hspan.trans_le (Nat.pow_le_pow_right (by decide) (by omega)), hretfit⟩

end NearQuarticWires.StageRecovery
