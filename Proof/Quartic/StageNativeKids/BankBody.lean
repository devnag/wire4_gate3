import Proof.Quartic.StageNativeKids.BankFormat
import Proof.Quartic.StageNativeKids.HeaderCopy
import Proof.Quartic.StageNativeKids.HeaderData

set_option autoImplicit false

namespace NearQuarticWires.StageNativeKids

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close NearCubicGates.Close.Interfaces NearCubicGates.Close.WordPrograms
open StageTuple

/-- `lem:print`, paper/paper.tex: the
retained selected source, affine header and original width occupy three
distinct physical tapes before the tagged original-pool call. -/
def bankFormatTapes : Fin 4 ↪ Fin 17 := ⟨![14, 15, 6, 16], by decide⟩

/-- `lem:print`, paper/paper.tex: the
bank bit is disjoint from all three cleared binary-copy registers. -/
def bankFormatRegisters : Fin 4 ↪ Fin 16 := ⟨![10, 0, 1, 3], by decide⟩

/-- `lem:print`, paper/paper.tex: actual
original-bank comparison, selected original source, affine-header copy
and finite tagged source emission form one physical source computation. -/
noncomputable def bankBodyProgram : WMX 16 16 :=
  .seq (bankSelectionProgram 4 7)
    (.seq (selectSourceProgram 2 14)
      (.seq (copyHeaderProgram 7 15 0 1 3)
        (.wm (bankFormatProgram bankFormatTapes bankFormatRegisters))))

/-- `prop:time`, paper/paper.tex: the
source-bank computation pays each small scalar, original byte, header
marker and width-codec copy once, with every sequence transition. -/
def bankBodyClock (r : NativeKidsRequest) : ℕ :=
  bankSelectionClock r.header.call.first.gates.length (r.toRowContext.originalIndex r.atom).val +
    selectSourceClock (r.toRowContext.originalIndex r.atom).val (callWord r.header.call).length +
    copyHeaderClock r.headerNaturals r.headerFlags +
    bankFormatClock (selectedSourceWord r.header.call.first.gates.length
      (r.toRowContext.originalIndex r.atom).val (callWord r.header.call))
      (r.toRowContext.rowHeader r.atom) r.outputWidth + 3

/-- `prop:time`, paper/paper.tex: every
source-bank scalar fits a fixed linear reserve in the actual retained
source lengths and the two polynomial original occurrence counters. -/
def bankBodyCapacity (r : NativeKidsRequest) : ℕ :=
  100 * (r.header.call.first.gates.length + (r.toRowContext.originalIndex r.atom).val +
    (callWord r.header.call).length +
    (selectedSourceWord r.header.call.first.gates.length
      (r.toRowContext.originalIndex r.atom).val (callWord r.header.call)).length +
    (r.toRowContext.rowHeader r.atom).length + (natWord r.outputWidth).length + 1) + 1000

/-- `lem:print` and `prop:time`, paper/paper.tex: actual retained original fields produce the
exact cold tagged pool source. All branch decisions, source and affine
metadata arise from those bytes; no gate, row or count is supplied. -/
theorem bankBody_run (r : NativeKidsRequest) (σ : WState 16 16)
    (hcall : σ.st 2 = frame (callWord r.header.call))
    (hcontext : σ.st 4 = r.contextWord) (hrole : σ.st 7 = r.rolePayload)
    (hwidth : σ.st 6 = natWord r.outputWidth)
    (hempty : ∀ i : Fin 17, i ∈ [14, 15, 16] → σ.st i = [])
    (hheads : ∀ i, σ.sh i = 0) (hzero : ∀ i, σ.val i = 0) :
    ∃ τ, WXExec (bankBodyCapacity r) bankBodyProgram σ τ (bankBodyClock r) ∧
      τ.st 16 = frame r.bankWord := by
  let cap := bankBodyCapacity r
  have hrow : r.headerNaturals.flatMap natWord ++ r.headerFlags =
      r.toRowContext.rowHeader r.atom := (rowHeader_bytes r).symm
  obtain ⟨selected, e1, hb⟩ := bankSelectionProgram_spec cap (4 : Fin 17) 7 (by decide)
    r.header.call.first.gates.length (r.toRowContext.originalIndex r.atom).val
    (natWord r.header.call.second.gates.length ++ natWord r.header.prepared.seedParameters.N ++
      natWord r.walkCode.val)
    (r.toRowContext.rowHeader r.atom) σ
    (by rw [hcontext]; simp [NativeKidsRequest.contextWord, List.append_assoc]) (by rw [hrole]; rfl) (hheads 4) (hheads 7) hzero
    (by dsimp [cap, bankBodyCapacity]; omega)
  obtain ⟨sourced, e2, hsourced⟩ := selectSourceProgram_spec cap (2 : Fin 17) 14 4 7
    (by decide) r.header.call.first.gates.length (r.toRowContext.originalIndex r.atom).val
    (callWord r.header.call) σ selected hb
    (by rw [hb.tapes]; exact hcall)
    (by rw [hb.heads]; simp [hheads])
    (by rw [hb.tapes]; exact hempty 14 (by decide))
    (by rw [hb.heads]; simp [hheads])
    (by dsimp [cap, bankBodyCapacity]; omega)
  subst sourced
  obtain ⟨headed, e3, hheaded⟩ := copyHeaderProgram_spec cap (7 : Fin 17) 15 (0 : Fin 16) 1 3
    (by decide) (by decide) (by decide) (by decide)
    r.headerNaturals r.headerFlags (natWord (r.toRowContext.originalIndex r.atom).val) []
    (headerNaturals_length r) (headerFlags_length r)
    (selected.sets 14 (frame (selectedSourceWord r.header.call.first.gates.length
      (r.toRowContext.originalIndex r.atom).val (callWord r.header.call))))
    (by simp only [WState.sets_st, Function.update_of_ne (show (7 : Fin 17) ≠ 14 by decide),
        hb.tapes, hrole, List.append_nil]; exact rolePayload_bytes r)
    (by rw [WState.sets_sh, hb.heads]; simp)
    (by rw [WState.sets_st]; simp [hb.tapes, hempty])
    (by rw [WState.sets_sh, hb.heads]; simp [hheads])
    (by rw [WState.sets_val]; exact hb.zeros 0 (by decide))
    (by rw [WState.sets_val]; exact hb.zeros 1 (by decide))
    (by rw [WState.sets_val]; exact hb.zeros 3 (by decide))
    (by rw [hrow]; dsimp [cap, bankBodyCapacity]; omega)
  subst headed
  have ef := bankFormatProgram_spec cap bankFormatTapes bankFormatRegisters
    (decide (r.header.call.first.gates.length ≤ (r.toRowContext.originalIndex r.atom).val))
    (selectedSourceWord r.header.call.first.gates.length
      (r.toRowContext.originalIndex r.atom).val (callWord r.header.call))
    (r.toRowContext.rowHeader r.atom) r.outputWidth
    (((selected.sets 14 (frame (selectedSourceWord r.header.call.first.gates.length
      (r.toRowContext.originalIndex r.atom).val (callWord r.header.call)))).sets 15
        (frame (r.headerNaturals.flatMap natWord ++ r.headerFlags))).seth 7
      ((natWord (r.toRowContext.originalIndex r.atom).val).length +
        (r.headerNaturals.flatMap natWord ++ r.headerFlags).length))
    (by simpa [bankFormatRegisters] using hb.second)
    (by simp [bankFormatTapes])
    (by simp [bankFormatTapes, hrow])
    (by simp [bankFormatTapes, hb.tapes, hwidth])
    (by intro i; fin_cases i <;> simp [bankFormatTapes, hb.heads, hheads])
    (by simp [bankFormatTapes, hb.tapes, hempty])
    (by simpa [bankFormatRegisters] using hb.zeros 0 (by decide))
    (by simpa [bankFormatRegisters] using hb.zeros 1 (by decide))
    (by simpa [bankFormatRegisters] using hb.zeros 3 (by decide))
    (by simp only [NearCubicWires.RepairOrdinary.frame_length]
        dsimp [cap, bankBodyCapacity]; omega)
  refine ⟨_, (e1.seq (e2.seq (e3.seq (.wm ef)))).mono ?_, ?_⟩
  · unfold bankBodyClock
    omega
  · simp [appendO, bankFormatTapes, NativeKidsRequest.bankWord, hb.tapes, hempty]

end NearQuarticWires.StageNativeKids
