import Proof.Quartic.StageNativeKids.PriceReduction
import Proof.Quartic.StageNativeKidsPoolPrice.Final

set_option autoImplicit false

namespace NearQuarticWires.StageNativeKids

open StageNativeKidsPrice

/-- `prop:time`, paper/paper.tex: the
complete actual one-atom native-provider budget has an unconditional
fixed structural price for every original source, atom and walk. -/
theorem native_budget_price :
    Price NativeKidsRequest.structuralScale NativeKidsRequest.budget :=
  budget_price_of_pool_price StageNativeKidsPoolPrice.actualPoolPrice

/-- `prop:time`, paper/paper.tex: the
entire actual source, native child loop and once-only resize budget is
polynomial in finite original source length, original arity and actual
target width, with no numeric radix or walk-code power. -/
theorem budget_polynomial : ∃ K e : ℕ, ∀ r : NativeKidsRequest,
    r.budget ≤ K * (r.word.length + r.header.call.n + r.outputWidth + 1)^e :=
  budget_polynomial_of_pool_price StageNativeKidsPoolPrice.actualPoolPrice

end NearQuarticWires.StageNativeKids
