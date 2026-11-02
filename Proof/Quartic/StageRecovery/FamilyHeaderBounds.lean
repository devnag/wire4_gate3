import Proof.Quartic.StageRecovery.FamilyHeader

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicWires NearCubicGates.Close.Cells NearCubicGates.Close.Expand
open NearCubicGates.Close.Interfaces.Formats

/-- `prop:time`, paper/paper.tex: every literal header
field has binary length bounded by the small structural setup hint. -/
theorem FamilyCompileRequest.header_bits (r : FamilyCompileRequest) :
    ∀ v ∈ r.header, natBitLength v ≤ r.setupHint + 2 := by
  let T := r.source.arity + r.source.formula.size +
    (formulaWord ⟨r.source.arity, r.source.formula⟩).length + natBitLength r.source.modulus + 10
  have hh := r.source.hint_sufficient
  change T ^ 2 ≤ r.source.hint at hh
  have hT : T ≤ r.source.hint + 1 := by nlinarith
  have htok : (tokenStream (toks r.source.formula)).length ≤
      (formulaWord ⟨r.source.arity, r.source.formula⟩).length := by
    simp only [formulaWord, NearCubicGates.Close.Interfaces.listWord, tokenStream, List.length_append]
    omega
  have hn := tokens_length_le_stream r.source.formula
  have hwidth := r.setupHint_width
  have hhint : r.source.hint ≤ r.setupHint := by unfold FamilyCompileRequest.setupHint; omega
  have hdegree : r.degree ≤ r.setupHint := by
    dsimp [FamilyCompileRequest.family, FamilyRequest.width] at hwidth
    omega
  have hbase := nbl_le_self r.setupHint
  have hD := nbl_le_self r.degree
  have hL := nbl_le_self (tokenStream (toks r.source.formula)).length
  have hH := nbl_le_self r.source.hint
  have hV := nbl_le_self r.source.arity
  have hN := nbl_le_self (toks r.source.formula).length
  dsimp [T] at hT
  intro v hv
  simp only [FamilyCompileRequest.header, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

/-- `prop:time`, paper/paper.tex: cold setup derives
its binary workspace from the real leading structural hint. -/
theorem FamilyCompileRequest.context_width (r : FamilyCompileRequest) :
    64 * (r.setupHint + 1) ≤ (ctxOf packetCallee pointSizes r.word).Wd := by
  change 64 * (r.setupHint + 1) ≤ 2 ^ (1 * leadOnes r.word) * 64
  rw [r.leading_hint, Nat.one_mul]
  have h := lt_natBitLength r.setupHint
  omega

end NearQuarticWires.StageRecovery
