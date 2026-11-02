import Proof.Quartic.StageCertNative.PriceReserve
import Proof.Quartic.StageCertNative.PriceOutputFinal
import Proof.Quartic.StageCertNativePoolCost.Cache

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative

/-- `prop:time`, paper/paper.tex: all
cached-source hypotheses of the actual native-field compiler are
discharged by its concrete once-context source programs. -/
theorem actual_nativeFields_price (B1 B2 : ℕ) :
    JobPrice (fun r : TermJob B1 B2=>nativeFieldsBudget r.base) 4 :=
  price_nativeFields (StageCertNativePoolCost.price_baseWordLength B1 B2)
    (StageCertNativePoolCost.price_cachedSourceBudget B1 B2)
    (StageCertNativePoolCost.price_cachedSourceLength B1 B2)
    (StageCertNativePoolCost.price_baseContextBudget B1 B2)

theorem original_nativeFields_budget (B1 B2 : ℕ) :
    OriginalPrice (@nativeFieldsBudget B1 B2) :=
  OriginalPrice.of_job_reserve (actual_nativeFields_price B1 B2) (by decide : 4≤50)

theorem original_base_word (B1 B2 : ℕ) :
    OriginalPrice (fun r : StageCertificateControl.IndexedRequest B1 B2=>r.baseWord.length) :=
  OriginalPrice.of_job_zero (StageCertNativePoolCost.price_baseWordLength B1 B2)

end NearQuarticWires.StageCertNative
