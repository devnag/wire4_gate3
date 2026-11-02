import Proof.Quartic.StagePrep.SampleProgram
import Proof.Quartic.StagePrep.SeedSizes

/-!
# The complete sample and seed computation

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch

/-- The consecutive exact sample-exponent and seed-size
operations of `sec:params`, paper/paper.tex. -/
def samplingStage : St VV := .seq sampleExponentProgram seedSizesProgram

/-- The sample computation in `sec:params`, paper/paper.tex, takes work linear in its exponent rather than
in its exponentially large binary sample-size value. -/
theorem samplingStage_spec (C : Ctx) (a : DS VV) (hc : Cst a)
    (N m o1 o2 num den k : ℕ) (eta : ℚ)
    (hNv : a.env nSideReg = N) (hmv : a.env mReg = m)
    (ho1v : a.env omegaOneReg = o1) (ho2v : a.env omegaTwoReg = o2)
    (huv : a.env etaNumReg = num) (hdv : a.env etaDenReg = den)
    (hkv : a.env pK = k) (hun : eta.num = num) (hdd : eta.den = den)
    (hN : 0 < N) (hm : 0 < m) (ho1 : 0 < o1) (ho2 : 0 < o2)
    (hu : 0 < num) (hd : 0 < den)
    (hW : 16 * (sampleNumerator N m (o1 * o2) den + sampleDenominator num) + 256 < 2 ^ C.Wd)
    (heW : Cells.ParameterArithmetic.sampleExponent N m (2 * (o1 * o2)) eta < C.Wd)
    (hseed : 2 * m * max k (Cells.ParameterArithmetic.sampleExponent N m (2 * (o1 * o2)) eta + 1) +
      k + Cells.ParameterArithmetic.sampleExponent N m (2 * (o1 * o2)) eta + 32 < 2 ^ C.Wd) :
    Hs C samplingStage a
      (30 * Cells.ParameterArithmetic.sampleExponent N m (2 * (o1 * o2)) eta + 20100)
      (fun b =>
        b.env qExponentReg = Cells.ParameterArithmetic.sampleExponent N m (2 * (o1 * o2)) eta ∧
        b.env qReg = 2 ^ Cells.ParameterArithmetic.sampleExponent N m (2 * (o1 * o2)) eta ∧
        b.env ellFieldReg = max k (Cells.ParameterArithmetic.sampleExponent N m (2 * (o1 * o2)) eta + 1) ∧
        b.env seedLengthReg = 2 * m * max k (Cells.ParameterArithmetic.sampleExponent N m (2 * (o1 * o2)) eta + 1) ∧
        b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
        FrS a b ([rationalNumReg, rationalDenReg, rationalCeilReg, t3, t5, t6, qExponentReg, vJ] ++
          [P2E, P2X, P2I, qReg, pX1, ellFieldReg, seedLengthReg, vJ])) := by
  let e := Cells.ParameterArithmetic.sampleExponent N m (2 * (o1 * o2)) eta
  have henc : e = (Nat.clog 2 (sampleArgument N m (o1 * o2) num den) + 3) / 4 := by
    dsimp only [e]
    rw [sampleExponent_encoding N m (o1 * o2) num den eta hun hdd hu hd, clog_sixteen]
  have hlog : Nat.clog 2 (sampleArgument N m (o1 * o2) num den) ≤ 4 * e := by omega
  unfold samplingStage
  refine Hx.hs (Hs.then (sampleExponentProgram_spec C a hc N m o1 o2 num den eta
    hNv hmv ho1v ho2v huv hdv hun hdd hN hm ho1 ho2 hu hd hW)
    (fun b ⟨hbe, hbcp, hbwq, hbout, hbc, hbfr⟩ n1 hn1 => ?_))
  have hbk : b.env pK = k := (hbfr _ (by decide) (by decide)).trans hkv
  have hbm : b.env mReg = m := (hbfr _ (by decide) (by decide)).trans hmv
  refine Hs.last (seedSizesProgram_spec C b hbc e k m hbe hbk hbm heW hseed) ?_
  rintro d ⟨hdQ, hdell, hdS, hdcp, hdwq, hdout, hdc, hdfr⟩ n2 hn2
  refine ⟨⟨?_, hdQ, hdell, hdS, hdcp.trans hbcp, hdwq.trans hbwq,
    hdout.trans hbout, hdc, FrS.trans (FrS.weaken hbfr (by decide))
      (FrS.weaken hdfr (by decide))⟩, ?_⟩
  · exact (hdfr _ (by decide) (by decide)).trans hbe
  · change n2 ≤ 5 * e + 80 at hn2
    change n1 ≤ 5 * Nat.clog 2 (sampleArgument N m (o1 * o2) num den) + 20000 at hn1
    omega

end NearQuarticWires.StagePrep
