import Proof.Quartic.StageNativeKids.Budget

set_option autoImplicit false

namespace NearQuarticWires.StageNativeKids

open StageNativeKidsPrice

/-- `prop:time`, paper/paper.tex: the
actual original-pool clock envelope, together with the checked source,
selector and resize-tail prices, bounds the complete concrete one-atom
budget without adding a gate, row, child or count assumption. -/
theorem budget_price_of_pool_price (hpool : StageNativeKidsPool.ActualPoolPrice) :
    Price NativeKidsRequest.structuralScale NativeKidsRequest.budget := by
  obtain ⟨K, e, hp⟩ := hpool
  have hboth : ∃ K e : ℕ,
      (∀ q : FirstBankRequest, StageNativeKidsPool.firstPoolBudget q ≤
        K * q.val.originalSourceScale ^ e) ∧
      (∀ q : SecondBankRequest, StageNativeKidsPool.secondPoolBudget q ≤
        K * q.val.originalSourceScale ^ e) := by
    refine ⟨K, e, ?_, ?_⟩
    · intro q
      exact hp ⟨q.val, false, q.property⟩
    · intro q
      exact hp ⟨q.val, true, q.property⟩
  have hselected : Price NativeKidsRequest.structuralScale selectedPoolBudget :=
    native_tagged_pool_price StageNativeKidsPool.firstPoolBudget StageNativeKidsPool.secondPoolBudget hboth
  have hsource := native_source_bank_price
  have htail := native_tail_price
  change Price NativeKidsRequest.structuralScale (fun r => r.budget)
  simp only [NativeKidsRequest.budget, poolSourceBudget]
  price_with structuralScale_pos

/-- `prop:time`, paper/paper.tex: the
unchanged cubic original-child cap converts the complete concrete
one-atom budget into a fixed polynomial of original source length,
original arity and actual target field width; no degree, numeric radix
or numeric walk-code exponent is introduced. -/
theorem budget_polynomial_of_pool_price (hpool : StageNativeKidsPool.ActualPoolPrice) :
    ∃ K e : ℕ, ∀ r : NativeKidsRequest,
      r.budget ≤ K * (r.word.length + r.header.call.n + r.outputWidth + 1)^e := by
  obtain ⟨K, e, hp⟩ := budget_price_of_pool_price hpool
  refine ⟨K * 40^e, 3 * e, fun r => ?_⟩
  calc
    r.budget ≤ K * r.structuralScale^e := hp r
    _ ≤ K * (40 * (r.word.length + r.header.call.n + r.outputWidth + 1)^3)^e :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (native_structural_scale_bound r) e)
    _ = (K * 40^e) * (r.word.length + r.header.call.n + r.outputWidth + 1)^(3 * e) := by
      rw [mul_pow, ← pow_mul]
      ring

end NearQuarticWires.StageNativeKids
