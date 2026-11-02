import Proof.Quartic.StageGamma.TermStep
import Proof.Quartic.StageGamma.PairTotal

set_option autoImplicit false

namespace NearQuarticWires.StageGamma

open NearCubicGates.Close.Cells

/-- `cor:conditional`, paper/paper.tex: each exact
address computes its complete ORIGINAL signed term and adds both sign
components to the physical accumulator. -/
def gammaEnumerationBody : St VV MM := .seq gammaTermStep accumulatePair

/-- `cor:conditional`, paper/paper.tex: the literal
ORIGINAL `(Q+1)^8` census is one counted finite-control loop. -/
def gammaEnumeration : St VV MM := forS gammaAddress gammaCensus gammaEnumerationBody

/-- `cor:conditional`, paper/paper.tex: the exact
address and both accumulated sums survive every complete term computation. -/
theorem termScratch_accumulators :
    gammaAddress ∉ termScratch ∧ gammaCensus ∉ termScratch ∧
    gammaPositiveSum ∉ termScratch ∧ gammaNegativeSum ∉ termScratch := by
  decide

/-- `cor:conditional`, paper/paper.tex: actual
accumulator writes do not change the ORIGINAL static data or loop bounds. -/
theorem staticRegisters_accumulators :
    (∀ x : Fin VV, x ∈ staticRegisters → x ∉ [gammaPositiveSum, gammaNegativeSum]) ∧
    (∀ x : Fin VV, x ∈ staticRegisters → x ≠ gammaAddress) := by
  decide

/-- `cor:conditional` and `prop:time`, paper/paper.tex: the actual exact-radix loop computes all ORIGINAL signed
terms once, physically accumulates them, preserves the static source and
charges only `(Q+1)^8` times a polynomial seed factor. -/
theorem gammaEnumeration_run (request : Machine.GammaRequest) (width : ℕ) (input : List Bool)
    (a : DS VV MM) (ha : StaticReady request a)
    (hp : a.env gammaPositiveSum = 0) (hn : a.env gammaNegativeSum = 0)
    (hwidth : 4 * Cycle.seedLength request.parameters + 10 ≤ width) :
    Hs (gaussContext width input (gaussInputReserve request) (gaussWorkReserve request))
      gammaEnumeration a
      ((request.parameters.Q + 1) ^ 8 *
        (2000010 * (Cycle.seedLength request.parameters + 9) ^ 6 + 8) + 4)
      (fun b => StaticReady request b ∧
        b.env gammaPositiveSum = (originalPartialPair request ((request.parameters.Q + 1) ^ 8)).positive ∧
        b.env gammaNegativeSum = (originalPartialPair request ((request.parameters.Q + 1) ^ 8)).negative ∧
        b.out = a.out) := by
  let C := gaussContext width input (gaussInputReserve request) (gaussWorkReserve request)
  let M := (request.parameters.Q + 1) ^ 8
  let T := 2000010 * (Cycle.seedLength request.parameters + 9) ^ 6 + 4
  let I : ℕ → DS VV MM → Prop := fun k b => StaticReady request b ∧
    b.env gammaPositiveSum = (originalPartialPair request k).positive ∧
    b.env gammaNegativeSum = (originalPartialPair request k).negative ∧ b.out = a.out
  have hfit : M < 2 ^ width := (choiceCount_le request).trans_lt
    (Nat.pow_lt_pow_right (by decide) (by omega))
  have hI : ∀ k b v, I k b → I k (b.set gammaAddress v) := by
    intro k b v ⟨hbs, hbp, hbn, hbo⟩
    have hc : Cst (b.set gammaAddress v) := Cst.of_fr (T := [gammaAddress])
      hbs.header.2.2.2.2 (Fr.set b v (by simp)) (by decide)
    refine ⟨StaticReady.preserve_registers request hbs
      (fun x hx => DS.set_env_ne _ _ (staticRegisters_accumulators.2 x hx))
      rfl hbs.header.2.2.2.1 hc,
      by rw [DS.set_env_ne _ _ (by decide)]; exact hbp,
      by rw [DS.set_env_ne _ _ (by decide)]; exact hbn, hbo⟩
  have h0 : I 0 a := by
    exact ⟨ha, by simpa [originalPartialPair] using hp,
      by simpa [originalPartialPair] using hn, rfl⟩
  have hr := forS_spec' (C := C) gammaAddress gammaCensus (by decide) gammaEnumerationBody
    a M hfit I T hI h0 ha.census
  refine Hs.mono (hr ?_) le_rfl (fun _ h => h.1)
  intro k hk b ⟨hbs, hbp, hbn, hbo⟩ hindex hcensus
  let address : Fin ((request.parameters.Q + 1) ^ 8) := ⟨k, hk⟩
  have hquery := gammaTermStep_run request address width input b hbs hindex hwidth
  unfold gammaEnumerationBody
  refine Hs.seq (t1 := 2000010 * (Cycle.seedLength request.parameters + 9) ^ 6) (t2 := 3)
    hquery ?_
  intro d ⟨dp, dn, hds, dout, _, _, df⟩
  have dP : d.env gammaPositiveSum = (originalPartialPair request k).positive := by
    rw [df _ termScratch_accumulators.2.2.1]
    exact hbp
  have dN : d.env gammaNegativeSum = (originalPartialPair request k).negative := by
    rw [df _ termScratch_accumulators.2.2.2]
    exact hbn
  have termEq : indexedTermPair request k = originalTermPair request
      (littleChoiceEquiv request.parameters.Q address) := by
    have hk' : k < (request.parameters.Q + 1) ^ 8 := hk
    simp only [indexedTermPair, dif_pos hk']
    rfl
  refine Hs.mono (accumulatePair_run C request k hk d hds.header.2.2.2.2 dP dN
    (termEq ▸ dp) (termEq ▸ dn)
    (by change 3 * Cycle.seedLength request.parameters + 9 ≤ width; omega)) le_rfl ?_
  intro e ⟨ep, en, es, ec, ef⟩
  have hes := StaticReady.preserve_registers request hds
    (fun x hx => ef x (staticRegisters_accumulators.1 x hx)) es.ip
    (es.kin.trans hds.header.2.2.2.1) ec
  refine ⟨⟨hes, ep, en, es.out.trans (dout.trans hbo)⟩, ?_, ?_⟩
  · rw [ef _ (by decide), df _ termScratch_accumulators.1]
    exact hindex
  · rw [ef _ (by decide), df _ termScratch_accumulators.2.1]
    exact hcensus

end NearQuarticWires.StageGamma
