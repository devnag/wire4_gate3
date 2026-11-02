import Proof.Quartic.StageTupleSetup.BankLayout

set_option autoImplicit false

namespace NearQuarticWires.StageTupleSetup.BankLayout

variable {widthTapes rowTapes coefficientTapes : ℕ}

local notation "wB" => widthBank (widthTapes:=widthTapes) (rowTapes:=rowTapes) (coefficientTapes:=coefficientTapes)
local notation "rB" => rowBank (widthTapes:=widthTapes) (rowTapes:=rowTapes) (coefficientTapes:=coefficientTapes)
local notation "zB" => zeroBank (widthTapes:=widthTapes) (rowTapes:=rowTapes) (coefficientTapes:=coefficientTapes)
local notation "tB" => twoBank (widthTapes:=widthTapes) (rowTapes:=rowTapes) (coefficientTapes:=coefficientTapes)

/-- `lem:print`, paper/paper.tex: all actual
private one-shot helper banks are pairwise disjoint, so one cold helper
never changes the next helper's retained input or fresh work tapes. -/
theorem width_row_ne (i : Fin widthTapes) (j : Fin rowTapes) : wB i≠rB j := by
  intro he
  have hh:=congrArg Fin.val he
  change 24+i.val=24+widthTapes+j.val at hh
  have hi:=i.isLt
  omega

theorem width_zero_ne (i : Fin widthTapes) (j : Fin coefficientTapes) : wB i≠zB j := by
  intro he
  have hh:=congrArg Fin.val he
  change 24+i.val=24+widthTapes+rowTapes+j.val at hh
  have hi:=i.isLt
  omega

theorem width_two_ne (i : Fin widthTapes) (j : Fin coefficientTapes) : wB i≠tB j := by
  intro he
  have hh:=congrArg Fin.val he
  change 24+i.val=24+widthTapes+rowTapes+coefficientTapes+j.val at hh
  have hi:=i.isLt
  omega

theorem row_zero_ne (i : Fin rowTapes) (j : Fin coefficientTapes) : rB i≠zB j := by
  intro he
  have hh:=congrArg Fin.val he
  change 24+widthTapes+i.val=24+widthTapes+rowTapes+j.val at hh
  have hi:=i.isLt
  omega

theorem row_two_ne (i : Fin rowTapes) (j : Fin coefficientTapes) : rB i≠tB j := by
  intro he
  have hh:=congrArg Fin.val he
  change 24+widthTapes+i.val=24+widthTapes+rowTapes+coefficientTapes+j.val at hh
  have hi:=i.isLt
  omega

theorem zero_two_ne (i j : Fin coefficientTapes) : zB i≠tB j := by
  intro he
  have hh:=congrArg Fin.val he
  change 24+widthTapes+rowTapes+i.val=24+widthTapes+rowTapes+coefficientTapes+j.val at hh
  have hi:=i.isLt
  omega

end NearQuarticWires.StageTupleSetup.BankLayout
