import Proof.Quartic.StagePrint.EntryReaderCost
import Proof.Quartic.StageEntryAllocation.Allocation

set_option autoImplicit false

namespace NearQuarticWires.StagePrint.EntryFormat
open NearCubicWires NearCubicWires.RepairOrdinary

/-- `prop:time`, paper/paper.tex: the clock
belongs to the actual fixed original-arity formatter and includes its
complete source read, byte output and ordinary machine resets. -/
noncomputable def formatterBudget {C E : ℕ} {modular : Bool}
    (r : BoundedRequest C E modular) : ℕ :=
  allocatedBudget (StageEntryAllocation.allocation C E modular) r

/-- `lem:print`, paper/paper.tex: one actual
ordinary machine transforms the unchanged literal source into the
framed existing Tuple input, deriving all real lengths and widths.
Exact and modular modes differ only in the interpretation of the
physically read scale field. -/
noncomputable def formatterWordFunction (C E : ℕ) (modular : Bool) :
    WordFunction (BoundedRequest C E modular) BoundedRequest.word
      (fun r=>frame r.toRequest.termRequest.word) formatterBudget :=
  formatterWithAllocation (StageEntryAllocation.allocation C E modular)

/-- `prop:time`, paper/paper.tex: the actual
formatter clock is linear in its finite Terms/source bytes, with one
fixed original-arity polynomial multiplier and no Terms-count square. -/
theorem formatterBudget_linear (C E : ℕ) (modular : Bool) :
    ∃ K e : ℕ,∀ r : BoundedRequest C E modular,
      formatterBudget r≤K*(r.word.length+1)*(r.header.call.n+1)^e :=
  allocatedBudget_linear (StageEntryAllocation.allocation C E modular)

end NearQuarticWires.StagePrint.EntryFormat
