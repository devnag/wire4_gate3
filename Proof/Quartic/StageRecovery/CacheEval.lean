import Proof.Quartic.StageRecovery.InputReturn
import Proof.Quartic.StageRecovery.ModPointBounds

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicGates.Close.Cells NearCubicGates.Close.Expand NearCubicGates.Close.Tabulator
open NearCubicGates.Close.Interfaces.Formats

/-- `lem:print`, paper/paper.tex: a cached value is
computed from the original retained Formula token bytes, after which
the input head is returned by one paid step per consumed bit. -/
def cachedEvaluationProgram : St VV MM :=
  .seq (.op (.zero stackVar)) (.seq modularTokenLoop inputReturnProgram)

/-- `lem:print`, paper/paper.tex: one complete cached
evaluation retains the characteristic point and every cache cursor. -/
def cachedEvaluationScratch : List (Fin VV) := inputReturnIndex :: tokenCounterVar :: evalScratch

/-- `prop:time`, paper/paper.tex: each cached Formula
value pays its original token stream and its linear physical head return. -/
def cachedEvaluationCost {V : ℕ} (F : Formula V) : ℕ :=
  (toks F).length * (500 * (formulaTokenBound F + 10) + 4) +
    5 * (tokenStream (toks F)).length + 12

/-- `lem:print`, paper/paper.tex: one actual modular
evaluation and paid input return preserve the entire non-register state,
so the unchanged literal Formula can be reused for the next cached point. -/
theorem cachedEvaluationProgram_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    {V : ℕ} (F : Formula V) (q point : ℕ) (suffix : List Bool)
    (hq : 2 ≤ q) (haq : a.env modulusVar = q) (hap : a.env pointVar = point)
    (hcount : a.env tokenCountVar = (toks F).length)
    (hcountfit : (toks F).length < 2 ^ C.Wd)
    (hin : C.inp.drop a.ip = tokenStream (toks F) ++ suffix)
    (hwidth : formulaTokenBound F + 5 ≤ C.Wd)
    (hdepth : q ^ ((toks F).length + 3) ≤ 2 ^ C.Wd)
    (hlength : a.env tokenLengthVar = (tokenStream (toks F)).length)
    (hlengthfit : (tokenStream (toks F)).length < 2 ^ C.Wd) :
    Hs C cachedEvaluationProgram a (cachedEvaluationCost F) (fun b =>
      b.env stackVar = (modAlg q point).eval F ∧ b.sh = a.sh ∧
      Cst b ∧ Fr a b cachedEvaluationScratch) := by
  unfold cachedEvaluationProgram cachedEvaluationCost
  refine (Hs.seq (t2 := ((toks F).length * (500 * (formulaTokenBound F + 10) + 4) + 4) +
    (5 * (tokenStream (toks F)).length + 4) + 1) (hs_zero C stackVar a)
    fun b hb => ?_).mono (by omega) (fun _ h => h)
  subst b
  let start := a.set stackVar 0
  have hstartc : Cst start := Cst.of_fr (T := [stackVar]) hc (Fr.set _ _ (by decide)) (by decide)
  refine Hs.seq (modularTokenLoop_suffix_spec C start hstartc q point (toks F) suffix
    (formulaTokenBound F) hq
    (by simpa (config := {decide := true}) [start, DS.set] using haq)
    (by simpa (config := {decide := true}) [start, DS.set] using hap) rfl
    (by simpa (config := {decide := true}) [start, DS.set] using hcount)
    hcountfit hin (tokenBound_le_formula F) hwidth hdepth) fun b ⟨hbs, _, _, hbi, hbr, hbc, hbf⟩ => ?_
  have hbl : b.env tokenLengthVar = (tokenStream (toks F)).length := by
    rw [hbf _ (by decide)]
    simpa (config := {decide := true}) [start, DS.set] using hlength
  refine (inputReturnProgram_spec C b _ a.ip hbl hbi hlengthfit).mono le_rfl ?_
  rintro d ⟨hdi, hdr, hdf⟩
  refine ⟨?_, ?_, Cst.of_fr hbc hdf (by decide), ?_⟩
  · rw [hdf _ (by decide)]
    rw [Alg.foldl_toks_nil] at hbs
    simpa only [senc, Nat.mul_zero, Nat.add_zero] using hbs
  · change (d.ip, formulaRest d) = (a.ip, formulaRest a)
    rw [hdi]
    exact congrArg (fun x => (a.ip, x)) (hdr.trans hbr)
  · exact Fr.trans (Fr.set _ _ (by decide))
      (Fr.trans (Fr.weaken hbf (by intro y hy; simp [cachedEvaluationScratch] at hy ⊢; tauto))
        (Fr.weaken hdf (by simp [cachedEvaluationScratch])))

end NearQuarticWires.StageRecovery
