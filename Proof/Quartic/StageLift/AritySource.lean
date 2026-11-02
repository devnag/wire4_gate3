import Proof.Quartic.StageCert.FrequencyCounts
import Proof.Quartic.StageLift.DegreeProgram

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open StageCert.Tokens

/-- `lem:print`, paper/paper.tex: the Formula
arity is physically computed from both original occurrence banks. -/
def printArityVar : Fin VV := 57

/-- `lem:print`, paper/paper.tex: the literal
seventeen-role pool includes every original occurrence in both banks. -/
def computePrintArity : St VV MM :=
  .seq loadOccurrenceCounts (.seq (setK degreeFactor 17)
    (.op (.mul atomCount degreeFactor printArityVar)))

/-- `lem:print`, `sec:params` and `prop:time`, paper/paper.tex: actual retained frequency
records supply G1,G2 and the exact V=17(G1+G2) header, including empty
banks. The occurrence cap is never substituted for the actual census. -/
theorem computePrintArity_spec (C : Ctx) (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (a : DS VV MM) (hc : Cst a)
    (hparams : a.ram parameterStore = parameterScalars p)
    (hW : 5 ≤ C.Wd) (hfit : 17 * (Builder.allGates c).length < 2 ^ C.Wd) :
    Hs C computePrintArity a (a.rc parameterStore + 367) (fun b =>
      b.env printArityVar = 17 * (Builder.allGates c).length ∧
      b.env atomCount = (Builder.allGates c).length ∧
      b.env firstGateCount = c.first.gates.length ∧ b.rc parameterStore = 16 ∧
      StageMain.parameterRest b = StageMain.parameterRest a ∧ Cst b ∧
      Fr a b [t2, vJ, c0, atomValue, tupleQuotient, tupleRemainder,
        firstGateCount, atomCount, degreeFactor, printArityVar]) := by
  have hG : c.first.gates.length + c.second.gates.length = (Builder.allGates c).length := by
    simp only [Builder.allGates, List.length_append]
  have hcount : c.first.gates.length + c.second.gates.length < 2 ^ C.Wd := by omega
  have h17 : 17 < 2 ^ C.Wd := by
    have hh := Nat.pow_le_pow_right (show 1 ≤ (2 : ℕ) by decide) hW
    norm_num at hh
    omega
  unfold computePrintArity
  refine (Hs.seq (t1 := a.rc parameterStore + 327) (t2 := 39)
    (loadOccurrenceCounts_run C c hs a hc hparams hW hcount)
    fun b ⟨hbf, hbG, hbcur, hbrest, hbc, hbfr⟩ => ?_).mono (by omega) (fun _ h => h)
  rw [hG] at hbG
  refine Hs.seq (t1 := 37) (t2 := 1) (setK_spec degreeFactor (by decide) 17 b h17)
    fun d ⟨h17d, hdsh, hdfr⟩ => ?_
  have hdG : d.env atomCount = (Builder.allGates c).length :=
    (hdfr _ (by decide)).trans hbG
  refine (hs_mul C atomCount degreeFactor printArityVar d (by decide) (by decide) (by decide)
    (by rw [hdG, h17d]; simpa only [Nat.mul_comm] using hfit)).mono le_rfl ?_
  rintro z rfl
  have hsame := Same.of_sh hdsh
  have hf : Fr a (d.set printArityVar (d.env atomCount * d.env degreeFactor))
      [t2, vJ, c0, atomValue, tupleQuotient, tupleRemainder,
        firstGateCount, atomCount, degreeFactor, printArityVar] :=
    (hbfr.weaken (by simp)).trans ((hdfr.weaken (by simp)).trans (Fr.set _ _ (by simp)))
  refine ⟨?_, ?_, ?_, ?_, ?_, Cst.of_fr hc hf (by decide), hf⟩
  · simp only [DS.set_env_self, hdG, h17d, Nat.mul_comm]
  · rw [DS.set_env_ne _ _ (by decide)]
    exact hdG
  · rw [DS.set_env_ne _ _ (by decide), hdfr _ (by decide)]
    exact hbf
  · change d.rc parameterStore = 16
    rw [hsame.rc]
    exact hbcur
  · simpa only [StageMain.parameterRest, DS.set, hsame.ip, hsame.out, hsame.ram,
      hsame.rc, hsame.kin, hsame.kout, hsame.kc] using hbrest

end NearQuarticWires.StageLift
