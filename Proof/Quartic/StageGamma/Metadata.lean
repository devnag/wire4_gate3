import Proof.Quartic.StageGamma.CellPrepare

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageGamma

open NearCubicGates.Close.Cells

/-- `cor:conditional`, paper/paper.tex: a fixed
scratch loop counter forms the actual side length once. -/
def gammaPowerIndex : Fin VV := ⟨62, by decide⟩

/-- `cor:conditional`, paper/paper.tex: the actual
side length N is obtained by paid binary shifts of the ORIGINAL kh. -/
def prepareSide : St VV MM :=
  binaryPower gammaPowerIndex (requestFieldRegister 1) gammaSide

/-- `cor:conditional` and `prop:time`, paper/paper.tex: physical setup computes the ORIGINAL side length in
O(kh) binary operations, preserving every original field and cached modulus. -/
theorem prepareSide_run (C : Ctx) (request : Machine.GammaRequest)
    (a : DS VV MM) (hc : Cst a)
    (hkh : a.env (requestFieldRegister 1) = request.parameters.kh)
    (hwidth : request.parameters.kh < C.Wd) :
    Hs C prepareSide a (5 * request.parameters.kh + 6) (fun b =>
      b.env gammaSide = request.parameters.N ∧ Same a b ∧ Cst b ∧
      Fr a b [gammaPowerIndex, gammaSide]) :=
  binaryPower_run C gammaPowerIndex (requestFieldRegister 1) gammaSide
    (by decide) (by decide) (by decide) (by decide) a hc request.parameters.kh hkh hwidth

/-- `cor:conditional`, paper/paper.tex: the residual
seed length and cell projection width are formed by real binary operations. -/
def prepareWidths : St VV MM :=
  .seq (.op (.copy gammaCellWidth (requestFieldRegister 1)))
    (.seq (.op (.shl gammaCellWidth))
      (.seq (.op (.copy gammaRest (requestFieldRegister 0)))
        (.seq (.op (.shl gammaRest)) (.seq (.op (.shl gammaRest))
          (.seq (.op (.shl gammaRest)) (.op (.sub gammaRest (requestFieldRegister 3))))))))

/-- `cor:conditional` and `prop:time`, paper/paper.tex: every nonconstant width and column ruler used by the compact
Gaussian producer is computed from the ORIGINAL request at constant cost. -/
theorem prepareWidths_run (C : Ctx) (request : Machine.GammaRequest)
    (a : DS VV MM) (hc : Cst a)
    (hell : a.env (requestFieldRegister 0) = request.parameters.ell)
    (hkh : a.env (requestFieldRegister 1) = request.parameters.kh)
    (hplen : a.env (requestFieldRegister 3) = request.prefixLength)
    (hwidth : Cycle.seedLength request.parameters ≤ C.Wd) :
    Hs C prepareWidths a 13 (fun b =>
      b.env gammaRest = Cycle.seedLength request.parameters - request.prefixLength ∧
      b.env gammaCellWidth = 2 * request.parameters.kh ∧ Same a b ∧ Cst b ∧
      Fr a b [gammaRest, gammaCellWidth]) := by
  have hseed : Cycle.seedLength request.parameters < 2 ^ C.Wd := by
    exact hwidth.trans_lt (show C.Wd < 2 ^ C.Wd from Nat.lt_two_pow_self)
  have hkseed : 2 * request.parameters.kh ≤ Cycle.seedLength request.parameters := by
    have := request.parameters.k_le
    dsimp [Cycle.seedLength]
    omega
  unfold prepareWidths
  refine Hs.seq (t1 := 1) (t2 := 11)
    (hs_copy C gammaCellWidth (requestFieldRegister 1) a (by decide)) ?_
  intro b hb
  subst hb
  refine Hs.seq (t1 := 1) (t2 := 9)
    (hs_shl C gammaCellWidth _ (by vsimp [hkh]; omega)) ?_
  intro b hb
  subst hb
  refine Hs.seq (t1 := 1) (t2 := 7)
    (hs_copy C gammaRest (requestFieldRegister 0) _ (by decide)) ?_
  intro b hb
  subst hb
  refine Hs.seq (t1 := 1) (t2 := 5)
    (hs_shl C gammaRest _ (by vsimp [hell]; dsimp [Cycle.seedLength] at hseed; omega)) ?_
  intro b hb
  subst hb
  refine Hs.seq (t1 := 1) (t2 := 3)
    (hs_shl C gammaRest _ (by vsimp [hell]; dsimp [Cycle.seedLength] at hseed; omega)) ?_
  intro b hb
  subst hb
  refine Hs.seq (t1 := 1) (t2 := 1)
    (hs_shl C gammaRest _ (by vsimp [hell]; dsimp [Cycle.seedLength] at hseed; omega)) ?_
  intro b hb
  subst hb
  refine Hs.mono (hs_sub C gammaRest (requestFieldRegister 3) _ (by decide)
    (by
      vsimp [hell, hplen]
      have hh := request.prefixFits
      dsimp [Cycle.seedLength] at hh
      omega)) le_rfl ?_
  rintro b rfl
  refine ⟨by vsimp [hell, hplen, Cycle.seedLength]; omega, by vsimp [hkh],
    ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,
    ⟨by vsimp [hc.z], by vsimp [hc.one], by vsimp [hc.two]⟩, ?_⟩
  intro x hx
  have hxr : x ≠ gammaRest := by intro h; exact hx (by simp [h])
  have hxk : x ≠ gammaCellWidth := by intro h; exact hx (by simp [h])
  simp only [DS.set, Function.update_of_ne hxr, Function.update_of_ne hxk]

end NearQuarticWires.StageGamma
