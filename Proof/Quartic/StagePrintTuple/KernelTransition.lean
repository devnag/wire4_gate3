import Proof.Quartic.StagePrintTuple.KernelState
import Proof.Quartic.StagePrintTuple.HistoryClose

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm

/-- `lem:print`, paper/paper.tex: one completed
Cartesian iteration appends only its new tuple segment and advances
the actual tuple product and common row stride. -/
def KernelData.nextCartesian (data : KernelData) (records : List Bool) (K N : ℕ) : KernelData :=
  {data with
    history := data.history++records++[false]
    historyHead := data.history.length
    stride := data.stride+N
    children := 0
    tuples := K*data.tuples}

/-- `lem:print`, paper/paper.tex: literal state
updates produced by history closing and real tuple counters coincide
with the next exact boundary; no other source or cache is changed. -/
theorem KernelData.nextCartesian_state (data : KernelData) (records : List Bool)
    (K N span : ℕ) (r : TermCutRequest) :
    (data.nextCartesian records K N).state span r=
      (((closedHistory (data.state span r) (kernelLocal span 20) 0 data.history records).setv
        14 (K*data.tuples)).setv 13 0).setv 12 (data.stride+N) := by
  apply WState.eq
  · funext i
    by_cases hi:i.val=20
    · have he:i=kernelLocal span 20 := Fin.ext hi
      subst i
      simp [KernelData.nextCartesian,KernelData.state,closedHistory,kernelLocal]
    · have he:i≠kernelLocal span 20 := by intro h;exact hi (congrArg Fin.val h)
      simp [KernelData.nextCartesian,KernelData.state,closedHistory,he,hi]
  · funext i
    by_cases hi:i.val=20
    · have he:i=kernelLocal span 20 := Fin.ext hi
      subst i
      simp [KernelData.nextCartesian,KernelData.state,closedHistory,kernelLocal]
    · have he:i≠kernelLocal span 20 := by intro h;exact hi (congrArg Fin.val h)
      simp [KernelData.nextCartesian,KernelData.state,closedHistory,he,hi]
  · funext i
    fin_cases i <;> simp [KernelData.nextCartesian,KernelData.state,closedHistory]
  · rfl

end NearQuarticWires.StageTuple
