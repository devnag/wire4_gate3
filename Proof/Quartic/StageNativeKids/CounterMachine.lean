import Proof.Quartic.StageNativeKids.Selection

set_option autoImplicit false

namespace NearQuarticWires.StageNativeKids

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces
open StageTuple StagePrint

/-- `lem:print`, paper/paper.tex: the
first branch retains the actual original request and only the proved
result of comparing its original occurrence with the first bank size. -/
abbrev FirstBankRequest := {r : NativeKidsRequest //
  (r.toRowContext.originalIndex r.atom).val < r.header.call.first.gates.length}

/-- `lem:print`, paper/paper.tex: the
second branch retains the original request and actual first-bank offset,
without a selected gate, row, child or count supplied as an input. -/
abbrev SecondBankRequest := {r : NativeKidsRequest //
  r.header.call.first.gates.length ≤ (r.toRowContext.originalIndex r.atom).val}

/-- `prop:time`, paper/paper.tex: the
first branch pays the real source-selected original compiler and real
record counter, including their complete finite word handoff. -/
noncomputable def firstCountBudget (r : FirstBankRequest) : ℕ :=
  indexedOriginalCountBudget (firstCountSource r.val r.property)

/-- `prop:time`, paper/paper.tex: the
second branch pays the same actual original compilation and record
counting after its real relative occurrence index is computed. -/
noncomputable def secondCountBudget (r : SecondBankRequest) : ℕ :=
  indexedOriginalCountBudget (secondCountSource r.val r.property)

/-- `imp:disjoint` and `lem:print`, paper/paper.tex: original first-bank source bytes produce the
exact native child count, including zero, by the real compiler and
record counter; no child or count is supplied by the caller. -/
noncomputable def firstCountWordFunction :
    WordFunction FirstBankRequest
      (fun r => natWord (r.val.toRowContext.originalIndex r.val.atom).val ++ callWord r.val.header.call)
      (fun r => frame (natWord (r.val.toRowContext.nativeKids r.val.atom).length)) firstCountBudget :=
  ⟨(indexedOriginalCountPrinter false).program, by
    intro r
    have h := (indexedOriginalCountPrinter false).realizes (firstCountSource r.val r.property)
    rw [firstCountSource_count] at h
    simpa only [firstCountBudget,
      RawBits.IndexedCallGateRequest.source, firstCountSource, List.append_nil]
      using h⟩

/-- `imp:disjoint` and `lem:print`, paper/paper.tex: source-selected second-bank compilation and
actual record counting compute the identical native-pool census, with
the original first-bank offset removed and every tie preserved. -/
noncomputable def secondCountWordFunction :
    WordFunction SecondBankRequest
      (fun r => natWord ((r.val.toRowContext.originalIndex r.val.atom).val -
        r.val.header.call.first.gates.length) ++ callWord r.val.header.call)
      (fun r => frame (natWord (r.val.toRowContext.nativeKids r.val.atom).length)) secondCountBudget :=
  ⟨(indexedOriginalCountPrinter true).program, by
    intro r
    have h := (indexedOriginalCountPrinter true).realizes (secondCountSource r.val r.property)
    rw [secondCountSource_count] at h
    simpa only [secondCountBudget,
      RawBits.IndexedCallGateRequest.source, secondCountSource, List.append_nil]
      using h⟩

end NearQuarticWires.StageNativeKids
