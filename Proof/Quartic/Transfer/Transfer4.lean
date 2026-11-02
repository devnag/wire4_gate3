import Proof.Quartic.Transfer.Supply4

/-!
# The almost-everywhere transfer for the wire measure (paper Appendix A, `prop:ae-final`)

`transfer4`: the counting theorem `thm:counter` (`CounterExists4`) implies the main theorem for `SYM∘THR` circuits
measured by wires (`FinalStatement4'`), from the published inputs. The weak machine `M_wire` of §A.4 for the wire
counter is `NearQuarticWires.Worker4.WorkerArith.workerSupply4`. The chain is `closureSupply4_of` (§A.2, §A.7), `final4_of_closureSupply4` (`frontier4_of_closure4`:
schedule, `lem:ae-amplified`, `lem:ae-table`, recovery) and `mainStatement4_of_native_frontier4` (`prop:ae-final`).
-/

set_option autoImplicit false

namespace NearQuarticWires.Transfer

/-- **The wire-measure transfer.** -/
theorem transfer4 (hC : CounterExists4) : FinalStatement4' :=
  final4_of_closureSupply4 (closureSupply4_of hC)

end NearQuarticWires.Transfer
