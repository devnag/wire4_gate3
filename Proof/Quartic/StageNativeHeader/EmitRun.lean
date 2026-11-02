import Proof.Quartic.StageNativeHeader.EmitCost

/-!
# The emission of the native table request

Paper: `lem:print`, paper/paper.tex, and `prop:time`.

`emitP` appends to the accumulator, in order: `d`, `p`, the cut count and the content of the column field, then the
cut bytes, each bit at depth three; the fixed marks and the unary fields `q`, `U²` and `q − 1` at depth two; the
empty fields; and rewinds the accumulator. `emitCore_exec`: from the state of `EmitReady`, the accumulator holds the
pieces of `marks_table_word`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearQuarticWires.StageNativeHeader

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearQuarticWires.Control

/-- **The emission.** -/
noncomputable def emitP : WM hns hnr :=
  .seq (numP sZd wRd) (.seq (numP sZp wRp) (.seq (numP sZG wRG) (.seq (copyP sY) (.seq (copyP sIN)
  (.seq (emitList sACC eOP tailA) (.seq qP (.seq (unaryP rQ) (.seq (emitList sACC eOP ([true, false] ++ tailA))
  (.seq uP (.seq sqP (.seq (emitList sACC eOP [true, false]) (.seq (.dec rV) (.seq (unaryP rV)
  (.seq (emitList sACC eOP tail7) (WM.rewind sACC eOP)))))))))))))))

/-- The accumulator holds `a`, its head and its counter at its end. -/
def AccAt (τ : WState hns hnr) (a : List Bool) : Prop :=
  τ.st sACC = a ∧ τ.sh sACC = a.length ∧ τ.val eOP = a.length

theorem AccAt.next {σ τ : WState hns hnr} {a u : List Bool} {L : List (Fin hnr)} {S : List (Fin (hns + 1))}
    (h : AccAt σ a) (m : Emitted σ τ u L S) : AccAt τ (a ++ u) :=
  ⟨by rw [m.acc, h.1], by rw [m.acch, h.2.1, List.length_append], by rw [m.op, h.2.2, List.length_append]⟩

theorem AccAt.ho {τ : WState hns hnr} {a : List Bool} (h : AccAt τ a) : τ.sh sACC = (τ.st sACC).length := by
  rw [h.1, h.2.1]

/-- The registers the emission may change. -/
def emT : List (Fin hnr) := [eOZd, eOZp, eOZG, eSC, rQ, rV, rK1, rU, eK2, eK3, eOP]

/-- The streams the emission may change. -/
noncomputable def emS : List (Fin (hns + 1)) := [sZd, sZp, sZG, sY, sIN]

/-- The total length of the emitted word. -/
def outLen (nd np nG nC ns U q : ℕ) : ℕ := 8 * (nd + np + nG + nC + ns) + 4 * q + 4 * (U * U) + 4 * (q - 1) + 30

/-- The cost of the emission. -/
def coreCost (d p G nC ns U q : ℕ) : ℕ :=
  numCost d + numCost p + numCost G + nC * 81 + ns * 81 + 72 * q + 36 * q + 36 * (q - 1) +
    (d * (18 * 2 ^ d + 7) + 18 * d) + (U * (54 * U + 9) + 18 * U) +
    5 * outLen (2 * natBitLength d + 1) (2 * natBitLength p + 1) (2 * natBitLength G + 1) nC ns U q + 500

end NearQuarticWires.StageNativeHeader
