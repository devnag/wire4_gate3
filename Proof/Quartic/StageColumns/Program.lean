import Proof.Quartic.StageColumns.Payload
import Proof.Quartic.StageColumns.Source
import Proof.Quartic.StageRecovery.OutputFrame
import Proof.Gates.Cells.Prelude

set_option autoImplicit false

namespace NearQuarticWires.StageColumns

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicGates.Close.Cells

/-- `lem:print`, paper/paper.tex: the original
four-field parser is followed by the literal common-generator writer. -/
def rawProgram : St VV MM := .seq sourceProgram payloadProgram

def rawClock (P : StarParams) : ℕ := 1000 * (P.n + 2) + columnsClock P

/-- `imp:partition`, `lem:print` and `prop:time`, paper/paper.tex: the original serialized
metadata physically produces the exact unframed columns-field payload. -/
theorem rawProgram_run (C : Ctx) (a : DS VV MM) (P : StarParams)
    (hc : Cst a) (hip : a.ip = 0) (hinput : C.inp = columnInput P)
    (hwidth : P.n + 4 ≤ C.Wd) :
    Hs C rawProgram a (rawClock P) (fun b =>
      b.out = a.out ++ (natWord (PrimT.C4Geo.width P) ++ columnStream P)) := by
  unfold rawProgram rawClock
  refine (Hs.seq (t2 := 40 * (P.n + 1) + 43 + columnsClock P)
    (sourceProgram_run C a P hc hip hinput hwidth)
    (fun b ⟨hp, _, hrest⟩ => ?_)).mono (by omega) (fun _ hs => hs)
  refine (payloadProgram_run C b P hp hwidth).mono le_rfl ?_
  intro d hd
  have hout : b.out = a.out := congrArg Prod.fst hrest
  simpa only [hout] using hd

def rawColdProgram : St VV MM := .seq initP rawProgram

/-- `lem:print` and `prop:time`, paper/paper.tex: all constants are initialized in the actual zero state. -/
theorem rawColdProgram_run (C : Ctx) (P : StarParams)
    (hinput : C.inp = columnInput P) (hwidth : P.n + 4 ≤ C.Wd) :
    Hs C rawColdProgram (a0 : DS VV MM) (rawClock P + 6) (fun b =>
      b.out = natWord (PrimT.C4Geo.width P) ++ columnStream P) := by
  have htwo : 2 < 2 ^ C.Wd := by
    have hh : 2 ^ 2 ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (by decide) (by omega)
    norm_num at hh ⊢
    omega
  unfold rawColdProgram
  refine (Hs.seq (t1 := 5) (t2 := rawClock P)
    (initP_spec (C := C) (a0 : DS VV MM) rfl rfl rfl htwo) ?_).mono
    (by omega) (fun _ h => h)
  rintro a ⟨hc, _, _, hip, hout, _, _, _, _⟩
  refine (rawProgram_run C a P hc hip hinput hwidth).mono le_rfl ?_
  intro b hb
  simpa only [hout, a0, List.nil_append] using hb

/-- `lem:print`, paper/paper.tex: one final physical
framing transformation supplies precisely the columns field's outer frame. -/
def program : St VV MM := StageRecovery.OutputFrame.framedProgram rawColdProgram

def sourceClock (P : StarParams) : ℕ := 3 * (rawClock P + 6) + 2

/-- `imp:partition`, `lem:print` and `prop:time`, paper/paper.tex: the genuine cold program
returns the exact already-framed canonical columns field, without any
supplied generator table, coordinate provider or decoded metadata. -/
theorem program_run (C : Ctx) (P : StarParams)
    (hinput : C.inp = columnInput P) (hwidth : P.n + 4 ≤ C.Wd) :
    Hs C program (a0 : DS VV MM) (sourceClock P) (fun b =>
      b.out = PrimT.C4Geo.colsField P) := by
  obtain ⟨b, n, he, hn, hb⟩ := rawColdProgram_run C P hinput hwidth
  refine ⟨StageRecovery.OutputFrame.framedState b, 3 * n + 2,
    StageRecovery.OutputFrame.framedProgram_spec he, by unfold sourceClock; omega, ?_⟩
  change frame b.out = PrimT.C4Geo.colsField P
  rw [hb, colsField_stream]

end NearQuarticWires.StageColumns
