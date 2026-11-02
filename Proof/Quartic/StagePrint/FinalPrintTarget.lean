import Proof.Quartic.Program.Final
import Proof.Quartic.StagePrint.GreedyNativeScale
import Proof.Quartic.StagePrint.NativeMiddleTarget

set_option autoImplicit false

namespace NearQuarticWires.StagePrint.FinalTarget
open NearCubicWires

/-- `lem:print`, `lem:residue` and `prop:time`, paper/paper.tex: the actual complete table computation
uses the existing published counting input and supplies all fields of
the concrete program subroutine, including its own selected cost. -/
abbrev Supplier := Bindings.Williams14.Williams14_Corollary4_4 →
  (B1 B2 : ℕ) → Program.PrintField B1 B2

#check Program.PrintField
#check StageGreedyNativeData.nativeSupplier
#check StageGreedyNativeData.header_word_eq
#check GreedyCost.native_scale_le
#check GreedyCost.native_bit_parameter_polynomial

end NearQuarticWires.StagePrint.FinalTarget
