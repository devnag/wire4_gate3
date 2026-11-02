import Proof.Quartic.StageRecovery.CompilerBudget

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells NearCubicGates.Close.Expand

/-- `prop:time`, paper/paper.tex: the physical cold
cache-and-coefficient machine has quadratic support census and cubic
structural-hint cost, including all binary compilation and cleanup. -/
theorem FamilyCompileRequest.termsCacheBudget_le (r : FamilyCompileRequest) :
    r.termsCacheBudget ≤ 10 ^ 16 * (TSK packetCallee + 10) *
      ((famPairs r.source.arity r.degree).length + 1) ^ 2 * (r.setupHint + 1) ^ 3 := by
  let A := (famPairs r.source.arity r.degree).length + 1
  let H := r.setupHint + 1
  have hL : leadOnes r.cacheInput ≤ H := by
    rw [r.cacheInput_leading]
    exact nbl_le_self _
  have hW : 2 ^ leadOnes r.cacheInput * 64 ≤ 128 * H := by
    rw [r.cacheInput_leading]
    have h := NearCubicGates.Close.CounterMachine.PrefixProg.pow_nbl_le r.setupHint
    dsimp [H]
    omega
  have hn := r.compileTermsSteps_le
  have hpositive : 1 ≤ A ^ 2 * H := by
    have hpos : 0 < A ^ 2 * H := by dsimp [A, H]; positivity
    omega
  exact pointLangBudget_le r.cacheInput (3 * r.compileTermsSteps + 2) A H
    (by dsimp [A]; omega) (by dsimp [H]; omega) hL hW
    (by change r.compileTermsSteps ≤ 20000 * A ^ 2 * H at hn; nlinarith)
    r.cacheInput_length_le

/-- `prop:time`, paper/paper.tex: the actual original
source-to-native-input formatter has linear-in-setup-hint source clock,
before its separate finite-family computation. -/
theorem FamilyCompileRequest.formatterSteps_le (r : FamilyCompileRequest) :
    r.formatterSteps ≤ 10000 * (r.setupHint + 1) := by
  have hh := r.headerCost_le
  have hd := r.clock_dimensions
  have hwidth := r.setupHint_width
  have hdim : r.family.width + r.family.arity + r.family.degree + 1 ≤ 2 * (r.setupHint + 1) := by
    dsimp [FamilyCompileRequest.family, FamilyRequest.width] at hwidth ⊢
    omega
  unfold FamilyCompileRequest.formatterSteps
  nlinarith

/-- `prop:time`, paper/paper.tex: the cold actual
formatter's compiled physical clock is cubic in the structural setup hint. -/
theorem FamilyCompileRequest.formatterBudget_le (r : FamilyCompileRequest) :
    r.formatterBudget ≤ 10 ^ 16 * (TSK packetCallee + 10) * (r.setupHint + 1) ^ 3 := by
  let H := r.setupHint + 1
  have hL : leadOnes r.word ≤ H := by rw [r.leading_hint]; exact nbl_le_self _
  have hW : 2 ^ leadOnes r.word * 64 ≤ 128 * H := by
    rw [r.leading_hint]
    have h := NearCubicGates.Close.CounterMachine.PrefixProg.pow_nbl_le r.setupHint
    dsimp [H]
    omega
  have hs := r.formatterSteps_le
  change r.formatterSteps ≤ 10000 * H at hs
  have hH : 1 ≤ H := by dsimp [H]; omega
  have h := pointLangBudget_le r.word (3 * r.formatterSteps + 2) 1 H (by omega) hH hL hW
    (by simpa only [Nat.one_pow, Nat.mul_one] using (show 3 * r.formatterSteps + 2 ≤ 10 ^ 6 * H by nlinarith))
    (by have hi := r.word_length_le; dsimp [H] at *; nlinarith)
  simpa only [FamilyCompileRequest.formatterBudget, H, Nat.one_pow, Nat.mul_one] using h

/-- `prop:time`, paper/paper.tex: the genuine framed
native family-generator budget has a linear family count and at most a
quadratic setup-hint factor, independent of any original polynomial value. -/
theorem FamilyCompileRequest.familyFrameBudget_le (r : FamilyCompileRequest) :
    2 * familyFrameSteps r.family + 2 ≤
      10 ^ 10 * ((famPairs r.source.arity r.degree).length + 1) * (r.setupHint + 1) ^ 2 := by
  have hb := framedFamilyBudget_le r.family
  have hlen : (fam r.source.arity r.degree).length = (famPairs r.source.arity r.degree).length := by
    rw [fam_eq_pairs, List.length_map]
  have hd : (r.source.arity + r.degree + 9) ^ 2 ≤ r.setupHint + 1 := by
    unfold FamilyCompileRequest.setupHint
    calc (r.source.arity + r.degree + 9) ^ 2 ≤ (r.degree + r.source.arity + 10) ^ 2 :=
        Nat.pow_le_pow_left (by omega) _
      _ ≤ _ := by omega
  have hfour : (r.source.arity + r.degree + 9) ^ 4 ≤ (r.setupHint + 1) ^ 2 := by
    calc (r.source.arity + r.degree + 9) ^ 4 = ((r.source.arity + r.degree + 9) ^ 2) ^ 2 := by ring
      _ ≤ (r.setupHint + 1) ^ 2 := Nat.pow_le_pow_left hd _
  dsimp [FamilyCompileRequest.family] at hb
  rw [hlen] at hb
  exact hb.trans (Nat.mul_le_mul_left _ hfour)

/-- `prop:time`, paper/paper.tex: original-input
formatting and framed native family generation remain additive under
the actual ordinary-machine sequential composition. -/
theorem FamilyCompileRequest.sourceFamilyBudget_le (r : FamilyCompileRequest) :
    r.sourceFamilyBudget ≤ 10 ^ 18 * (TSK packetCallee + 10) *
      ((famPairs r.source.arity r.degree).length + 1) ^ 2 * (r.setupHint + 1) ^ 3 := by
  let A := (famPairs r.source.arity r.degree).length + 1
  let H := r.setupHint + 1
  let F := A ^ 2 * H ^ 3
  have ha : 1 ≤ A := by dsimp [A]; omega
  have hh : 1 ≤ H := by dsimp [H]; omega
  have hH3 : H ^ 3 ≤ F := Nat.le_mul_of_pos_left _ (by positivity)
  have hAH2 : A * H ^ 2 ≤ F := Nat.mul_le_mul
    (Nat.le_self_pow (by norm_num) A) (Nat.pow_le_pow_right hh (by omega))
  have hpositive : 1 ≤ F := by
    have hp : 0 < F := by dsimp [F]; positivity
    omega
  have hFT : F ≤ (TSK packetCallee + 10) * F := Nat.le_mul_of_pos_left _ (by omega)
  have hf := r.formatterBudget_le
  have hn := r.familyFrameBudget_le
  change r.formatterBudget ≤ 10 ^ 16 * (TSK packetCallee + 10) * H ^ 3 at hf
  change 2 * familyFrameSteps r.family + 2 ≤ 10 ^ 10 * A * H ^ 2 at hn
  have hfmt : r.formatterBudget ≤ 10 ^ 16 * (TSK packetCallee + 10) * F :=
    hf.trans (Nat.mul_le_mul_left _ hH3)
  have hnat : 2 * familyFrameSteps r.family + 2 ≤ 10 ^ 10 * F := by
    calc _ ≤ 10 ^ 10 * A * H ^ 2 := hn
      _ ≤ 10 ^ 10 * F := by nlinarith [hAH2]
  unfold FamilyCompileRequest.sourceFamilyBudget
  rw [show 10 ^ 18 * (TSK packetCallee + 10) * A ^ 2 * H ^ 3 =
    10 ^ 18 * (TSK packetCallee + 10) * F by dsimp [F]; ring]
  nlinarith

/-- `prop:time`, paper/paper.tex: retaining the
original Formula once pays one linear complete-source copy and the
single actual native-family computation. -/
theorem FamilyCompileRequest.retainedFamilyBudget_le (r : FamilyCompileRequest) :
    r.retainedFamilyBudget ≤ 10 ^ 20 * (TSK packetCallee + 10) *
      ((famPairs r.source.arity r.degree).length + 1) ^ 2 * (r.setupHint + 1) ^ 3 := by
  let A := (famPairs r.source.arity r.degree).length + 1
  let H := r.setupHint + 1
  let F := A ^ 2 * H ^ 3
  have ha : 1 ≤ A := by dsimp [A]; omega
  have hh : 1 ≤ H := by dsimp [H]; omega
  have hAH : A * H ≤ F := Nat.mul_le_mul
    (Nat.le_self_pow (by norm_num) A) (Nat.le_self_pow (by norm_num) H)
  have hpositive : 1 ≤ F := by
    have hp : 0 < F := by dsimp [F]; positivity
    omega
  have hFT : F ≤ (TSK packetCallee + 10) * F := Nat.le_mul_of_pos_left _ (by omega)
  have hsrc := r.sourceFamilyBudget_le
  have hinput := r.cacheInput_length_le
  change r.sourceFamilyBudget ≤ 10 ^ 18 * (TSK packetCallee + 10) * A ^ 2 * H ^ 3 at hsrc
  change (r.word ++ r.family.output).length ≤ 100 * A * H at hinput
  rw [List.length_append] at hinput
  have hsrcF : r.sourceFamilyBudget ≤ 10 ^ 18 * (TSK packetCallee + 10) * F := by
    calc r.sourceFamilyBudget ≤ 10 ^ 18 * (TSK packetCallee + 10) * A ^ 2 * H ^ 3 := hsrc
      _ = _ := by dsimp [F]; ring
  have hinputF : r.word.length + r.family.output.length ≤ 100 * F :=
    hinput.trans (by nlinarith [hAH])
  unfold FamilyCompileRequest.retainedFamilyBudget
  rw [show 10 ^ 20 * (TSK packetCallee + 10) * A ^ 2 * H ^ 3 =
    10 ^ 20 * (TSK packetCallee + 10) * F by dsimp [F]; ring]
  nlinarith

/-- `prop:time`, paper/paper.tex: the actual cold
general-modulus Formula-to-Terms compiler, including native support
generation, source retention, complete coefficient scans and canonical
output, has the sharp quadratic family census times a cubic setup hint. -/
theorem FamilyCompileRequest.modularTermsBudget_le (r : FamilyCompileRequest) :
    r.modularTermsBudget ≤ 10 ^ 22 * (TSK packetCallee + 10) *
      ((famPairs r.source.arity r.degree).length + 1) ^ 2 * (r.setupHint + 1) ^ 3 := by
  have hc := r.termsCacheBudget_le
  have hr := r.retainedFamilyBudget_le
  have hpositive : 1 ≤ (TSK packetCallee + 10) *
      ((famPairs r.source.arity r.degree).length + 1) ^ 2 * (r.setupHint + 1) ^ 3 := by
    have hp : 0 < (TSK packetCallee + 10) *
        ((famPairs r.source.arity r.degree).length + 1) ^ 2 * (r.setupHint + 1) ^ 3 := by positivity
    omega
  unfold FamilyCompileRequest.modularTermsBudget
  nlinarith

end NearQuarticWires.StageRecovery
