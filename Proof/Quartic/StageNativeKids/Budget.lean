import Proof.Quartic.StageNativeKids.Selected
import Proof.Quartic.StageNativeKids.TaggedPool
import Proof.Quartic.StageNativeKidsPool.Budget

set_option autoImplicit false

namespace NearQuarticWires.StageNativeKids

/-- `prop:time`, paper/paper.tex: the
computed original bank selects exactly one of the two concrete original
child-pool budgets, including its actual source and answer copies. -/
noncomputable def selectedPoolBudget (r : NativeKidsRequest) : ℕ :=
  taggedPoolBudget StageNativeKidsPool.firstPoolBudget StageNativeKidsPool.secondPoolBudget r

/-- `prop:time`, paper/paper.tex: the
whole original-to-native-pool source computation pays actual source
acquisition, actual bank selection and the selected actual pool, with
both real ordinary framed handoffs. -/
noncomputable def poolSourceBudget (r : NativeKidsRequest) : ℕ :=
  4 * sourceBankBudget r + 4 * selectedPoolBudget r + 12

/-- `prop:time`, paper/paper.tex: the
complete one-atom native provider pays its actual original source,
computed original-child pool and once-only native stream-resize tail,
including the final ordinary composition and exact output frame. -/
noncomputable def NativeKidsRequest.budget (r : NativeKidsRequest) : ℕ :=
  4 * poolSourceBudget r + 4 * r.resizeTailRequest.budget + 12

end NearQuarticWires.StageNativeKids
