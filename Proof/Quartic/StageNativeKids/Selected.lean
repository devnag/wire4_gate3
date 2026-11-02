import Proof.Quartic.StageNativeKids.AcquisitionPrice
import Proof.Quartic.Program.Pipe

set_option autoImplicit false

namespace NearQuarticWires.StageNativeKids

open NearCubicWires NearCubicWires.RepairOrdinary
open StageNativeKidsPrice

/-- `prop:time`, paper/paper.tex: the
original-source acquisition and cold bank selector are sequential real
ordinary calls, paying both complete clocks and the exact framed handoff. -/
noncomputable def sourceBankBudget (r : NativeKidsRequest) : ℕ :=
  4 * acquireBudget r + 4 * bankBudget r + 12

/-- `lem:print` and `prop:time`, paper/paper.tex: the literal original eleven-field input
computes its exact tagged source-selected bank request. The original
role, occurrence, bank, indexed call and affine header are all physically
obtained from those bytes, without any decoded source or count premise. -/
noncomputable def sourceBankWordFunction :
    WordFunction NativeKidsRequest NativeKidsRequest.word
      (fun r => frame r.bankWord) sourceBankBudget :=
  Program.WordFunction.pipe acquireWordFunction bankWordFunction

/-- `prop:time`, paper/paper.tex: the
complete original-to-tagged-source computation has one unconditional
structural polynomial budget, including both ordinary compositions. -/
theorem native_source_bank_price : Price NativeKidsRequest.structuralScale sourceBankBudget := by
  have ha := native_acquire_price
  have hb := native_bank_price
  change Price NativeKidsRequest.structuralScale
    (fun r => 4 * acquireBudget r + 4 * bankBudget r + 12)
  price_with structuralScale_pos

end NearQuarticWires.StageNativeKids
