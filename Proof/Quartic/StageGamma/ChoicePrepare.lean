import Proof.Quartic.StageGamma.StaticPrepare

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageGamma

open NearCubicGates.Close.Cells

/-- `cor:conditional`, paper/paper.tex: only the
true decoded digits, their labels and fixed arithmetic scratch vary from
one ORIGINAL coefficient choice to the next. -/
def choiceScratch : List (Fin VV) :=
  choiceDigitScratch (List.ofFn gammaDigit) ++ (List.finRange 8).map gammaLabel ++ [vJ]

/-- `cor:conditional`, paper/paper.tex: dynamic
choice preparation cannot overwrite ORIGINAL or cached static data. -/
theorem choiceScratch_static :
    (∀ i : Fin 14, requestFieldRegister i ∉ choiceScratch) ∧
    gammaModulus ∉ choiceScratch ∧ gammaRest ∉ choiceScratch ∧
    gammaCellWidth ∉ choiceScratch ∧ gammaSide ∉ choiceScratch ∧
    gammaBase ∉ choiceScratch ∧ gammaCensus ∉ choiceScratch ∧
    (∀ slot : Fin 8, gammaCell slot ∉ choiceScratch) := by
  constructor
  · intro i
    fin_cases i <;> decide
  · refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, ?_⟩
    intro slot
    fin_cases slot <;> decide

/-- `cor:conditional`, paper/paper.tex: complete
static ORIGINAL state survives the physical per-choice register changes. -/
theorem StaticReady.preserve_choice (request : Machine.GammaRequest) {a b : DS VV MM}
    (ha : StaticReady request a) (hs : Same a b) (hc : Cst b)
    (hf : Fr a b choiceScratch) : StaticReady request b := by
  have hn := choiceScratch_static
  refine ⟨⟨?_, ?_, hs.ip.trans ha.header.2.2.1,
    hs.kin.trans ha.header.2.2.2.1, hc⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [hf _ (hn.1 i)]
    exact ha.header.1 i
  · rw [hf _ hn.2.1]
    exact ha.header.2.1
  · rw [hf _ hn.2.2.1]
    exact ha.rest
  · rw [hf _ hn.2.2.2.1]
    exact ha.cellWidth
  · rw [hf _ hn.2.2.2.2.1]
    exact ha.side
  · intro slot
    rw [hf _ (hn.2.2.2.2.2.2.2 slot)]
    exact ha.cells slot
  · rw [hf _ hn.2.2.2.2.2.1]
    exact ha.base
  · rw [hf _ hn.2.2.2.2.2.2.1]
    exact ha.census

/-- `cor:conditional`, paper/paper.tex: exact
coefficient preparation decodes eight true radix digits and physically
forms their actual sample labels. -/
def choicePrepare : St VV MM := .seq decodeChoice prepareLabels

/-- `cor:conditional` and `prop:time`, paper/paper.tex: the complete ready bank for any ORIGINAL coefficient is
physically produced from its address and the once-prepared static state.
Every label, tie, prefix and Q=0 case is retained exactly. -/
theorem choicePrepare_run (C : Ctx) (request : Machine.GammaRequest)
    (address : Fin ((request.parameters.Q + 1) ^ 8)) (a : DS VV MM)
    (ha : StaticReady request a) (haddress : a.env gammaAddress = address.val)
    (hwidth : Cycle.seedLength request.parameters + 10 ≤ C.Wd) :
    Hs C choicePrepare a 77 (fun b =>
      BankReady request (littleChoiceEquiv request.parameters.Q address) b ∧
      StaticReady request b ∧ Same a b ∧ Fr a b choiceScratch) := by
  have hbase : 2 * (request.parameters.Q + 1) ≤ 2 ^ C.Wd := by
    have hQ := request.parameters.Q_le
    have hp : 1 ≤ 2 ^ request.parameters.ell := Nat.one_le_two_pow
    have hw : request.parameters.ell + 2 ≤ C.Wd := by
      dsimp [Cycle.seedLength] at hwidth
      omega
    have hexp := Nat.pow_le_pow_right (n := 2) (by decide) hw
    rw [show request.parameters.ell + 2 = request.parameters.ell + 1 + 1 by omega,
      pow_succ, pow_succ] at hexp
    omega
  unfold choicePrepare
  refine Hs.seq (t1 := 35) (t2 := 41)
    (decodeChoice_run C request.parameters.Q address a ha.header.2.2.2.2 ha.base haddress hbase) ?_
  intro b ⟨bdigits, bs, bc, bf⟩
  have bf' : Fr a b choiceScratch := bf.weaken (by
    intro x hx
    simpa only [choiceScratch, List.append_assoc] using
      (List.mem_append_left ((List.finRange 8).map gammaLabel ++ [vJ]) hx))
  have bh := StaticReady.preserve_choice request ha bs bc bf'
  refine Hs.mono (prepareLabels_run C request.parameters.Q
    (littleChoiceEquiv request.parameters.Q address) b bc bdigits) le_rfl ?_
  intro e ⟨elabels, es, ec, ef⟩
  have ef' : Fr b e choiceScratch := ef.weaken (by
    intro x hx
    simpa only [choiceScratch, List.append_assoc] using
      (List.mem_append_right (choiceDigitScratch (List.ofFn gammaDigit)) hx))
  have eh := StaticReady.preserve_choice request bh es ec ef'
  have efields := CachedHeader.fields request e eh.header
  refine ⟨⟨efields.1, efields.2.2.2.1, efields.2.2.2.2.1,
    eh.header.2.1, eh.rest, eh.cellWidth, ?_, elabels, eh.cells⟩,
    eh, bs.trans es, bf'.trans ef'⟩
  intro slot
  rw [ef (gammaDigit slot) (gammaDigit_not_labels slot (List.finRange 8))]
  exact bdigits slot

end NearQuarticWires.StageGamma
