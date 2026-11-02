import Proof.Quartic.StageTuplePreparedOutput.Head

set_option autoImplicit false

namespace NearQuarticWires.StageTuplePreparedOutput

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Interfaces.Formats
open StageTuple StageTupleSetup

variable {ns : ℕ}

/-- `prop:time`, paper/paper.tex: source
prefix and actual Terms output bytes have a linear additive bound. -/
theorem headBytes_le (P : Fin 10↪Fin (ns+1)) (r : TermCutRequest) :
    (headBytes P r).length ≤ cachesReserve (prefixFields P r)+2*(frame (termsWord r.terms)).length := by
  have hp := cachesBytes_le (prefixFields P r)
  simp only [headBytes, List.length_append, NearCubicGates.Close.Codec.marks_length]
  omega

/-- `prop:time`, paper/paper.tex: the
complete source-prefix formatting capacity stays linear in full source
bytes plus the Terms-independent structural magnitude. -/
theorem head_capacity (P : Fin 10↪Fin (ns+1)) (r : TermCutRequest) :
    cachesReserve (prefixFields P r)+(originalPrefix r).length+
      2*(frame (termsWord r.terms)).length+10 ≤ 1000*preparedOutputMagnitude r := by
  have hc := cache_reserve_le P r
  have hs := original_slice_le r
  have hS : 10 ≤ r.setupStructuralMagnitude := by unfold TermCutRequest.setupStructuralMagnitude; omega
  unfold preparedOutputMagnitude
  omega

/-- `prop:time`, paper/paper.tex: suffix
framing and the whole output rewind use the same linear capacity. -/
theorem finish_capacity (P : Fin 10↪Fin (ns+1)) (r : TermCutRequest) :
    (headBytes P r).length+cachesReserve (suffixFields P r)+10 ≤
      1000*preparedOutputMagnitude r := by
  have hb := headBytes_le P r
  have hc := cache_reserve_le P r
  have hs := original_slice_le r
  have hS : 10 ≤ r.setupStructuralMagnitude := by unfold TermCutRequest.setupStructuralMagnitude; omega
  unfold preparedOutputMagnitude
  omega

/-- `prop:time`, paper/paper.tex: all
actual copying, the unique Terms emission, finite control, final field
and whole output rewind fit the fixed linear complete-source clock. -/
theorem prepared_clock_le (P : Fin 10↪Fin (ns+1)) (r : TermCutRequest) :
    headClock P r+1+(cachesClock (suffixFields P r)+100+
      10*((headBytes P r).length+cachesReserve (suffixFields P r)+1)) ≤
      100000*preparedOutputMagnitude r := by
  have hp := cachesClock_le (prefixFields P r)
  have ht := cachesClock_le (suffixFields P r)
  have hc := cache_reserve_le P r
  have hb := headBytes_le P r
  have hs := original_slice_le r
  have hS : 10 ≤ r.setupStructuralMagnitude := by unfold TermCutRequest.setupStructuralMagnitude; omega
  unfold headClock preparedOutputMagnitude
  omega

end NearQuarticWires.StageTuplePreparedOutput
