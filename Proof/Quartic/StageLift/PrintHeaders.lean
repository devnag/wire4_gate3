import Proof.Quartic.StageLift.DegreeSource
import Proof.Quartic.StageLift.AritySource

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open StageCert.Tokens

/-- `lem:print` and `sec:params`, paper/paper.tex: actual parameter reads retain the exponent, chain length
and prime while computing the literal degree bound. -/
theorem computePrintDegree_fields_spec {x : Cells.ParameterInput} (C : Ctx)
    (p : Cells.Parameters) (hs : Cells.ParameterRules x p) (prime : ℕ)
    (a : DS VV MM) (hc : Cst a)
    (hparams : a.ram parameterStore = parameterScalars p)
    (hprime : a.env indexPrimeVar = prime) (hp : 2 ≤ prime)
    (hroom : 16 * p.Xmax + (2 * p.e - 1) * (2 * (p.J + 1)) * prime +
      2 * p.e + 2 * (p.J + 1) + prime + 17 < 2 ^ C.Wd) :
    Hs C computePrintDegree a (a.rc parameterStore + 401) (fun b =>
      b.env degreeVar = residueDegreeBound p prime ∧
      b.env degreeExponent = p.e ∧ b.env degreeChain = p.J ∧
      b.env degreePrime = prime ∧ b.ram = a.ram ∧
      (b.ip, b.out, b.kin, b.kout, b.kc) = (a.ip, a.out, a.kin, a.kout, a.kc) ∧
      b.rc parameterStore = 41 ∧ Cst b ∧
      Fr a b [degreeInput, degreeExponent, degreeChain, degreePrime, degreeVar,
        degreeFactor, degreeTerm, degreeProduct, vJ]) := by
  unfold computePrintDegree
  refine Hs.seq (t2 := 100) (readDegreeFields_spec C p prime a hc hparams hprime)
    fun b ⟨hbX, hbe, hbJ, hbp, hbcur, hbram, hbsh, hbc, hbf⟩ => ?_
  refine (computeResidueDegree_spec C b hbc p.Xmax p.e p.J prime hs.e_pos hs.J_pos hp
    hbX hbe hbJ hbp hroom).mono le_rfl ?_
  rintro d ⟨hdd, hdsh, hdc, hdf⟩
  have hsame := Same.of_sh hdsh
  refine ⟨hdd, (hdf _ (by decide)).trans hbe, (hdf _ (by decide)).trans hbJ,
    (hdf _ (by decide)).trans hbp, hsame.ram.trans hbram, ?_,
    by rw [hsame.rc, hbcur], hdc, ?_⟩
  · rw [hsame.ip, hsame.out, hsame.kin, hsame.kout, hsame.kc]
    exact hbsh
  · exact (hbf.weaken (by simp)).trans (hdf.weaken (by
      intro y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy ⊢
      tauto))

/-- `lem:print`, paper/paper.tex: actual scalar
records and original-bank frequencies supply both Formula headers. -/
def computePrintHeaders : St VV MM := .seq computePrintDegree computePrintArity

/-- `lem:print`, `sec:params` and `prop:time`, paper/paper.tex: degree, arity and all
residue-loop parameters are physically computed from retained input.
The original occurrence census is used in place of its upper bound. -/
theorem computePrintHeaders_spec (C : Ctx) (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (prime : ℕ)
    (a : DS VV MM) (hc : Cst a)
    (hparams : a.ram parameterStore = parameterScalars p)
    (hprime : a.env indexPrimeVar = prime) (hp : 2 ≤ prime)
    (hW : 5 ≤ C.Wd) (hfit : 17 * (Builder.allGates c).length < 2 ^ C.Wd)
    (hroom : 16 * p.Xmax + (2 * p.e - 1) * (2 * (p.J + 1)) * prime +
      2 * p.e + 2 * (p.J + 1) + prime + 17 < 2 ^ C.Wd) :
    Hs C computePrintHeaders a (a.rc parameterStore + 810) (fun b =>
      b.env degreeVar = residueDegreeBound p prime ∧
      b.env printArityVar = 17 * (Builder.allGates c).length ∧
      b.env degreeExponent = p.e ∧ b.env degreeChain = p.J ∧
      b.env degreePrime = prime ∧ b.env atomCount = (Builder.allGates c).length ∧
      b.env firstGateCount = c.first.gates.length ∧ b.ram = a.ram ∧
      (b.ip, b.out, b.kin, b.kout, b.kc) = (a.ip, a.out, a.kin, a.kout, a.kc) ∧
      b.rc parameterStore = 16 ∧ Cst b ∧
      Fr a b ([degreeInput, degreeExponent, degreeChain, degreePrime, degreeVar,
        degreeFactor, degreeTerm, degreeProduct, vJ] ++
        [t2, vJ, c0, atomValue, tupleQuotient, tupleRemainder,
          firstGateCount, atomCount, degreeFactor, printArityVar])) := by
  unfold computePrintHeaders
  have hd := computePrintDegree_fields_spec C p hs prime a hc hparams hprime hp hroom
  refine (Hs.seq (t1 := a.rc parameterStore + 401) (t2 := 408) hd
    fun b ⟨hbD, hbe, hbJ, hbp, hbram, hbsh, hbcur, hbc, hbfr⟩ => ?_).mono
      (by omega) (fun _ h => h)
  have ha := computePrintArity_spec C c hs b hbc (by rw [hbram]; exact hparams) hW hfit
  rw [hbcur] at ha
  refine ha.mono le_rfl ?_
  rintro d ⟨hdV, hdG, hdG1, hdcur, hdrest, hdc, hdfr⟩
  have hdram : d.ram = b.ram := congrArg (fun t => t.2.2.1) hdrest
  have hdsh : (d.ip, d.out, d.kin, d.kout, d.kc) =
      (b.ip, b.out, b.kin, b.kout, b.kc) :=
    congrArg (fun t => (t.1, t.2.1, t.2.2.2.2.1, t.2.2.2.2.2.1, t.2.2.2.2.2.2)) hdrest
  exact ⟨(hdfr _ (by decide)).trans hbD, hdV,
    (hdfr _ (by decide)).trans hbe, (hdfr _ (by decide)).trans hbJ,
    (hdfr _ (by decide)).trans hbp, hdG, hdG1, hdram.trans hbram,
    hdsh.trans hbsh, hdcur, hdc,
    (hbfr.weaken (by simp)).trans (hdfr.weaken (by simp))⟩

end NearQuarticWires.StageLift
