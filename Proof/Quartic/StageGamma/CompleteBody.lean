import Proof.Quartic.StageGamma.OutputFrame
import Proof.Quartic.StageGamma.PairPrint

set_option autoImplicit false

namespace NearQuarticWires.StageGamma

open NearCubicGates.Close.Cells

/-- `cor:conditional`, paper/paper.tex: the two
actual signed accumulator components are physically initialized to zero. -/
def initializeAccumulators : St VV MM :=
  .seq (.op (.zero gammaPositiveSum)) (.op (.zero gammaNegativeSum))

/-- `cor:conditional` and `prop:time`, paper/paper.tex: accumulator initialization preserves all ORIGINAL static
data and creates both zero registers by actual ordinary operations. -/
theorem initializeAccumulators_run (C : Ctx) (request : Machine.GammaRequest)
    (a : DS VV MM) (ha : StaticReady request a) :
    Hs C initializeAccumulators a 3 (fun b =>
      StaticReady request b ∧ b.env gammaPositiveSum = 0 ∧
      b.env gammaNegativeSum = 0 ∧ b.out = a.out) := by
  refine Hs.seq (t1 := 1) (t2 := 1) (hs_zero C gammaPositiveSum a) ?_
  intro b hb
  subst hb
  refine Hs.mono (hs_zero C gammaNegativeSum _) le_rfl ?_
  rintro b rfl
  have hf : Fr a ((a.set gammaPositiveSum 0).set gammaNegativeSum 0)
      [gammaPositiveSum, gammaNegativeSum] :=
    (Fr.set a _ (by simp)).trans (Fr.set _ _ (by simp))
  have hc : Cst ((a.set gammaPositiveSum 0).set gammaNegativeSum 0) :=
    Cst.of_fr ha.header.2.2.2.2 hf (by decide)
  exact ⟨StaticReady.preserve_registers request ha
    (fun x hx => hf x (staticRegisters_accumulators.1 x hx)) rfl ha.header.2.2.2.1 hc,
    by vsimp [], by simp, rfl⟩

/-- `cor:conditional`, paper/paper.tex: one fixed
ordinary program parses the retained ORIGINAL request, prepares its actual
static bank, enumerates exactly all choices and prints the signed numerator. -/
def gammaCachedBody : St VV MM :=
  .seq gammaPrelude (.seq initializeAccumulators (.seq gammaEnumeration printPair))

/-- `prop:time`, paper/paper.tex: all retained-source
decoding, exact census work and canonical signed output are included in
the actual complete source-language clock. -/
def gammaCachedBodyCost (request : Machine.GammaRequest) (width : ℕ) : ℕ :=
  600 * (Cycle.seedLength request.parameters + 9) +
    ((request.parameters.Q + 1) ^ 8 *
      (2000010 * (Cycle.seedLength request.parameters + 9) ^ 6 + 8) + 4) +
    40 * width + 136

/-- `cor:conditional` and `prop:time`, paper/paper.tex: the entire actual retained-source program computes the
required ORIGINAL signed conditional coefficient, including all zero,
negative, prefix and Q=0 cases, with no supplied Gaussian bank. -/
theorem gammaCachedBody_run (request : Machine.GammaRequest) (width : ℕ)
    (hwidth : 4 * Cycle.seedLength request.parameters + 10 ≤ width) :
    Hs (gaussContext width (cachedRequestWord request)
      (gaussInputReserve request) (gaussWorkReserve request)) gammaCachedBody
      (a0 : DS VV MM) (gammaCachedBodyCost request width)
      (fun b => b.out = NearCubicGates.Close.Interfaces.intWord (Machine.gammaTarget request)) := by
  let C := gaussContext width (cachedRequestWord request)
    (gaussInputReserve request) (gaussWorkReserve request)
  let enumCost := (request.parameters.Q + 1) ^ 8 *
    (2000010 * (Cycle.seedLength request.parameters + 9) ^ 6 + 8) + 4
  have hpre : Hs C gammaPrelude (a0 : DS VV MM)
      (600 * (Cycle.seedLength request.parameters + 9)) (fun b =>
        StaticReady request b ∧ b.out = []) := by
    obtain ⟨b, n, hex, hn, hb⟩ := gammaPrelude_run C request rfl
      (by change Cycle.seedLength request.parameters + 10 ≤ width; omega)
    exact ⟨b, n, hex, hn, hb, output_preserved hex gammaPrelude_no_output⟩
  unfold gammaCachedBody
  refine Hs.mono (Hs.seq (t1 := 600 * (Cycle.seedLength request.parameters + 9))
    (t2 := enumCost + 40 * width + 135) hpre ?_) (by dsimp [gammaCachedBodyCost]; omega)
    (fun _ h => h)
  intro b ⟨hb, hout⟩
  refine Hs.mono (Hs.seq (t1 := 3) (t2 := enumCost + (40 * width + 130) + 1)
    (initializeAccumulators_run C request b hb) ?_) (by omega) (fun _ h => h)
  intro d ⟨hd, hp, hn, hdout⟩
  refine Hs.seq (t1 := enumCost) (t2 := 40 * width + 130)
    (gammaEnumeration_run request width (cachedRequestWord request) d hd hp hn hwidth) ?_
  intro e ⟨he, ep, en, heout⟩
  have hmass := originalPartialPair_mass_le request ((request.parameters.Q + 1) ^ 8) le_rfl
  have hpow : 2 ^ (3 * Cycle.seedLength request.parameters + 8) < 2 ^ width :=
    Nat.pow_lt_pow_right (by decide) (by omega)
  have hpf : (originalPartialPair request ((request.parameters.Q + 1) ^ 8)).positive < 2 ^ C.Wd := by
    change _ < 2 ^ width
    omega
  have hnf : (originalPartialPair request ((request.parameters.Q + 1) ^ 8)).negative < 2 ^ C.Wd := by
    change _ < 2 ^ width
    omega
  refine Hs.mono (printPair_run C e he.header.2.2.2.2 _ _ ep en hpf hnf
    (by change 3 ≤ width; omega)) le_rfl ?_
  intro f hf
  rw [hf, heout, hdout, hout, List.nil_append]
  change NearCubicGates.Close.Interfaces.intWord
    (originalPartialPair request ((request.parameters.Q + 1) ^ 8)).value = _
  rw [originalPartialPair_full_value]

end NearQuarticWires.StageGamma
