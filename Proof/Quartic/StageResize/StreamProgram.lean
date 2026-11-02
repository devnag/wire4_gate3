import Proof.Quartic.StageResize.StreamLoop

set_option autoImplicit false

namespace NearQuarticWires.StageResize

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells
open StageLift

/-- `lem:print`, paper/paper.tex: decode only the
output width, then follow actual raw field markers to the real end bit. -/
def streamBodyProgram : St VV MM :=
  .seq (StageGamma.readField targetWidth) (.seq (.op (.rdI t0)) streamLoop)

def streamBodyClock (r : StreamResizeRequest) : ℕ :=
  30 * natBitLength r.outputWidth + streamLoopClock r.inputWidth r.outputWidth r.fieldCount + 60

/-- `lem:print` and `prop:time`, paper/paper.tex: the complete actual stream is consumed, including its
paid final marker; the output is exactly the raw resized record stream. -/
theorem streamBodyProgram_run (C : Ctx) (r : StreamResizeRequest) (a : DS VV MM)
    (hc : Cst a) (hin : C.inp.drop a.ip = r.word)
    (hwidth : r.outputWidth + natBitLength r.outputWidth + 4 ≤ C.Wd) :
    Hs C streamBodyProgram a (streamBodyClock r) (fun b =>
      b.out = a.out ++ r.output ∧ b.ip = a.ip + r.word.length) := by
  have hinput : C.inp.drop a.ip = natWord r.outputWidth ++
      (numberRecords r.inputWidth r.values ++ [false]) := by
    change C.inp.drop a.ip = natWord r.outputWidth ++
      NearCubicGates.Close.TabMachine.fieldsRecs r.inputWidth r.rows ++ [false] at hin
    rw [fieldsRecs_eq_numberRecords, List.append_assoc] at hin
    exact hin
  have hcap : r.outputWidth < 2 ^ C.Wd :=
    (show r.outputWidth ≤ C.Wd by omega).trans_lt Nat.lt_two_pow_self
  unfold streamBodyProgram
  refine Hx.hs (Hs.then (StageGamma.readField_spec C targetWidth (by decide) (by decide)
    a hc r.outputWidth (numberRecords r.inputWidth r.values ++ [false]) hinput (by omega)) ?_)
  rintro b ⟨bt, bip, brest, bc, _⟩ n0 hn0
  have bout : b.out = a.out := congrArg Prod.fst brest
  have bin : C.inp.drop b.ip = streamFlag r.values :: streamPayload r.inputWidth r.values := by
    rw [bip, ← List.drop_drop, hinput]
    simp only [List.drop_left]
    exact stream_decompose r.inputWidth r.input_pos r.values
  refine Hs.then (readInputBit_spec C t0 b (streamFlag r.values)
    (streamPayload r.inputWidth r.values) bin) ?_
  rintro d0 rfl n1 hn1
  let d : DS VV MM := { b.set t0 (streamFlag r.values).toNat with ip := b.ip + 1 }
  have dfr : Fr b d [t0] := Fr.set b _ (by simp)
  have dc : Cst d := bc.of_fr dfr (by decide)
  have dt : d.env targetWidth = r.outputWidth := by
    change (b.set t0 (streamFlag r.values).toNat).env targetWidth = _
    rw [DS.set_env_ne _ _ (by decide : targetWidth ≠ t0), bt]
  have din : C.inp.drop d.ip = streamPayload r.inputWidth r.values := by
    change C.inp.drop (b.ip + 1) = _
    rw [← List.drop_drop, bin]
    rfl
  refine Hs.last (streamLoop_run C r.inputWidth r.outputWidth r.input_pos r.width_le
    hcap r.values r.values_fit d dc (by simp [d]) dt din) ?_
  rintro e ⟨_, eip, eout, _, _⟩ n2 hn2
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [eout]
    change b.out ++ numberRecords r.outputWidth r.values = _
    rw [bout]
    congr 1
    exact (fieldsRecs_eq_numberRecords r.outputWidth r.rows).symm
  · rw [eip]
    change b.ip + 1 + (2 * r.inputWidth + 1) * r.values.length = _
    rw [bip]
    have hlen : r.word.length = (natWord r.outputWidth).length +
        (2 * r.inputWidth + 1) * r.values.length + 1 := by
      change (natWord r.outputWidth ++
        NearCubicGates.Close.TabMachine.fieldsRecs r.inputWidth r.rows ++ [false]).length = _
      rw [fieldsRecs_eq_numberRecords]
      simp only [List.length_append, List.length_singleton, numberRecords_length]
      rfl
    rw [hlen]
    omega
  · rw [r.values_length] at hn2
    unfold streamBodyClock
    omega

def streamProgram : St VV MM := .seq initP streamBodyProgram

def streamSourceClock (r : StreamResizeRequest) : ℕ := streamBodyClock r + 6

/-- `lem:print`, paper/paper.tex: the streaming
resizer starts from the actual zero state and emits only raw records. -/
theorem streamProgram_run (C : Ctx) (r : StreamResizeRequest) (hin : C.inp = r.word)
    (hwidth : r.outputWidth + natBitLength r.outputWidth + 4 ≤ C.Wd) :
    Hs C streamProgram (a0 : DS VV MM) (streamSourceClock r) (fun b => b.out = r.output) := by
  have htwo : 2 < 2 ^ C.Wd := by
    have hp : 4 ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (n := 2) (by decide)
      (show 2 ≤ C.Wd by omega)
    omega
  unfold streamProgram streamSourceClock
  refine (Hs.seq (t1 := 5) (t2 := streamBodyClock r)
    (initP_spec (C := C) (a0 : DS VV MM) rfl rfl rfl htwo) ?_).mono (by omega) (fun _ h => h)
  rintro a ⟨hc, _, _, hip, hout, _, _, _, _⟩
  refine (streamBodyProgram_run C r a hc (by
    rw [hip]
    change C.inp.drop 0 = r.word
    rw [List.drop_zero, hin]) hwidth).mono le_rfl ?_
  rintro b ⟨hb, _⟩
  simpa only [hout, a0, List.nil_append] using hb

end NearQuarticWires.StageResize
