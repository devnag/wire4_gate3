import Proof.Quartic.StageEntryAllocation.Cost

set_option autoImplicit false

namespace NearQuarticWires.StageEntryAllocation

/-- `lem:print` and `prop:time`, paper/paper.tex: one fixed original-arity allocator supplies both the
actual required width and the linear physical Cells budget in either mode. -/
def allocation (C E : ℕ) (modular : Bool) : StagePrint.EntryFormat.Allocation C E modular where
  sizes:=sizes C E
  required:=required_width C E modular
  linear_budget:=linear_budget C E modular

end NearQuarticWires.StageEntryAllocation
