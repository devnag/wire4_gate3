import Proof.Quartic.StageRecovery.ModPointBounds
import Proof.Gates.Cells.Prelude

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicWires NearCubicGates.Close.Cells NearCubicGates.Close.Expand
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Interfaces.Formats

/-- `lem:print`, paper/paper.tex: the complete actual
point evaluator reads the original Formula codec, evaluates every
postfix token modulo the recovery modulus and prints the reduced value. -/
def modularPointProgram : St VV MM :=
  .seq initP (.seq pointFieldsProgram (.seq (.op (.zero stackVar))
    (.seq modularTokenLoop (emitVariable stackVar))))

/-- `prop:time`, paper/paper.tex: the actual point
evaluator's source clock charges every field, literal token, modular
arithmetic operation and output bit. -/
def ModPointRequest.steps (r : ModPointRequest) : ℕ :=
  5 + (StageGamma.readFieldsCost r.fields +
    (1 + (((toks r.source.formula).length * (500 * (formulaTokenBound r.source.formula + 10) + 4) + 4) +
      (40 * natBitLength r.value + 42) + 1) + 1) + 1) + 1

/-- `lem:print`, paper/paper.tex: one actual cold
modular point evaluation consumes only the literal header and Formula
word and prints the exact reduced natural value. -/
theorem modularPointProgram_spec (C : Ctx) (r : ModPointRequest)
    (hin : C.inp = r.word) (hwidth : 64 * (r.source.hint + 1) ≤ C.Wd) :
    Hs C modularPointProgram (a0 : DS VV MM) r.steps
      (fun b => b.out = natWord r.value) := by
  obtain ⟨hfields, htokenwidth, hcountfit, hdepth⟩ := r.execution_bounds C hwidth
  have hW : 3 ≤ C.Wd := by omega
  have hp : C.Wd < 2 ^ C.Wd := Nat.lt_two_pow_self
  have hvbits := r.value_bits
  have hqbits : natBitLength r.source.modulus ≤ r.source.hint + 2 :=
    r.field_bits _ (by simp [ModPointRequest.fields])
  unfold modularPointProgram ModPointRequest.steps
  refine Hs.seq (initP_spec (C := C) (a0 : DS VV MM) rfl rfl rfl (by omega))
    fun a ⟨hc, _, _, hip, hout, _, _, _, _⟩ => ?_
  refine Hs.seq (pointFieldsProgram_spec C a hc r (by rw [hip]; simpa only [a0, List.drop_zero] using hin)
    hfields) fun b ⟨hbq, hbp, hbn, hbi, hbo, hbc⟩ => ?_
  refine Hs.seq (t2 := ((toks r.source.formula).length *
    (500 * (formulaTokenBound r.source.formula + 10) + 4) + 4) +
      (40 * natBitLength r.value + 42) + 1) (hs_zero C stackVar b) fun d hd => ?_
  subst d
  let base := b.set stackVar 0
  have hbasec : Cst base := Cst.of_fr (T := [stackVar]) hbc (Fr.set _ _ (by decide)) (by decide)
  have hinput : C.inp.drop base.ip = tokenStream (toks r.source.formula) := by
    change C.inp.drop b.ip = _
    rw [hbi, hip]
    simp only [a0, Nat.zero_add]
    rw [hin, r.word_eq, List.drop_left]
  have he := modularTokenLoop_spec C base hbasec r.source.modulus r.point (toks r.source.formula)
    (formulaTokenBound r.source.formula) r.source.modulus_ge_two
    (by simpa (config := {decide := true}) [base, DS.set] using hbq)
    (by simpa (config := {decide := true}) [base, DS.set] using hbp)
    (by simp [base])
    (by simpa (config := {decide := true}) [base, DS.set] using hbn) hcountfit hinput
    (tokenBound_le_formula r.source.formula) htokenwidth hdepth
  refine Hs.seq he fun d ⟨hds, _, _, _, hdo, hdc, _⟩ => ?_
  have hval : d.env stackVar = r.value := by
    rw [Alg.foldl_toks_nil] at hds
    simpa only [senc, Nat.mul_zero, Nat.add_zero, ModPointRequest.value] using hds
  have ep := emitVariable_spec C d hdc stackVar (by decide) (by omega)
    (by rw [hval]; omega)
  rw [hval] at ep
  refine ep.mono le_rfl ?_
  rintro e ⟨heo, _, _, _⟩
  rw [heo, hdo]
  change b.out ++ _ = _
  rw [hbo, hout]
  rfl

end NearQuarticWires.StageRecovery
