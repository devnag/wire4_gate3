import Proof.Quartic.StageNativeKids.TailPrice

set_option autoImplicit false

namespace NearQuarticWires.StageNativeKids

open NearCubicWires NearCubicWires.RepairOrdinary
open StageNativeKidsPrice

/-- `prop:time`, paper/paper.tex: the
existing ordinary selector charges exactly the branch chosen by the
computed original bank, using that branch's actual finite source and
count-plus-row reply and its charged cold computation. -/
def taggedPoolBudget (first : FirstBankRequest → ℕ) (second : SecondBankRequest → ℕ)
    (r : NativeKidsRequest) : ℕ :=
  StageMain.Tagged.taggedCost firstPoolWord (fun q : FirstBankRequest => q.val.resizeTailRequest.word)
    secondPoolWord (fun q : SecondBankRequest => q.val.resizeTailRequest.word)
    first second (actualBankRequest r)

/-- `lem:print`, paper/paper.tex: the
physically computed bank source and actual branch answer dock exactly
to the existing two-bank ordinary selector. -/
noncomputable def taggedPoolWordFunction {first : FirstBankRequest → ℕ}
    {second : SecondBankRequest → ℕ}
    (f : WordFunction FirstBankRequest firstPoolWord
      (fun q => frame q.val.resizeTailRequest.word) first)
    (g : WordFunction SecondBankRequest secondPoolWord
      (fun q => frame q.val.resizeTailRequest.word) second) :
    WordFunction NativeKidsRequest NativeKidsRequest.bankWord
      (fun r => frame r.resizeTailRequest.word) (taggedPoolBudget first second) :=
  ⟨(StageMain.Tagged.taggedWordFunction f g).program, by
    intro r
    have h := (StageMain.Tagged.taggedWordFunction f g).realizes (actualBankRequest r)
    rw [actualBankRequest_word, actualBankRequest_answer] at h
    exact h⟩

/-- `prop:time`, paper/paper.tex: the
actual tagged selector's entire physical charge is bounded by the real
branch price and actual bank-source and count-plus-row reply lengths;
the unused branch contributes no resource charge. -/
theorem taggedPoolBudget_bound (first : FirstBankRequest → ℕ) (second : SecondBankRequest → ℕ)
    (K e : ℕ)
    (hf : ∀ q, first q ≤ K * q.val.originalSourceScale ^ e)
    (hs : ∀ q, second q ≤ K * q.val.originalSourceScale ^ e)
    (r : NativeKidsRequest) :
    taggedPoolBudget first second r ≤ 200 * (r.bankWord.length +
      r.resizeTailRequest.word.length + K * r.originalSourceScale ^ e + 1) + 12 := by
  by_cases hb : r.header.call.first.gates.length ≤ (r.toRowContext.originalIndex r.atom).val
  · have hi := congrArg List.length (actualBankRequest_word r)
    simp only [actualBankRequest, dif_pos hb, StageMain.Tagged.taggedInput,
      List.length_cons] at hi
    have hp := hs ⟨r, hb⟩
    change second ⟨r, hb⟩ ≤ K * r.originalSourceScale ^ e at hp
    simp only [taggedPoolBudget, actualBankRequest, dif_pos hb, StageMain.Tagged.taggedCost]
    omega
  · have hi := congrArg List.length (actualBankRequest_word r)
    simp only [actualBankRequest, dif_neg hb, StageMain.Tagged.taggedInput,
      List.length_cons] at hi
    have hp := hf ⟨r, by omega⟩
    change first ⟨r, by omega⟩ ≤ K * r.originalSourceScale ^ e at hp
    simp only [taggedPoolBudget, actualBankRequest, dif_neg hb, StageMain.Tagged.taggedCost]
    omega

/-- `prop:time`, paper/paper.tex: a common
structural price for the two actual bank computations gives the exact
physical selector one fixed structural price, including both source
and answer copies. -/
theorem native_tagged_pool_price (first : FirstBankRequest → ℕ) (second : SecondBankRequest → ℕ)
    (hprice : ∃ K e : ℕ,
      (∀ q, first q ≤ K * q.val.originalSourceScale ^ e) ∧
      (∀ q, second q ≤ K * q.val.originalSourceScale ^ e)) :
    Price NativeKidsRequest.structuralScale (taggedPoolBudget first second) := by
  obtain ⟨K, e, hf, hs⟩ := hprice
  have hi := native_bank_word_price
  have ho := native_tail_word_price
  have hp : Price NativeKidsRequest.structuralScale NativeKidsRequest.originalSourceScale :=
    Price.of_le (by intro r; unfold NativeKidsRequest.structuralScale; omega)
  have h : Price NativeKidsRequest.structuralScale (fun r =>
      200 * (r.bankWord.length + r.resizeTailRequest.word.length +
        K * r.originalSourceScale ^ e + 1) + 12) := by
    price_with structuralScale_pos
  exact h.mono (taggedPoolBudget_bound first second K e hf hs)

end NearQuarticWires.StageNativeKids
