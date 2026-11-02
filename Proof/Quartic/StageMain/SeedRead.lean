import Proof.Quartic.StageMain.SeedReadLoop
import Proof.Quartic.Algorithm.Sound

/-!
# The framed chosen seed is decoded physically

`imp:seed`, paper/paper.tex, and Step 4 of
`sec:algorithm`: the source frame determines the
entire integer seed, including the empty word and leading zero bits.
The accumulator occupies only the width of the seed.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.SampleCells

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open StageLift
open Algorithm.CellCall (prefixValue)

def readSeed : St VV MM :=
  .seq (.op (.zero seed)) (.seq (.op (.copy seedPower v1))
    (.seq (.op (.rdI t0)) (.loop (.eq t0 v1) seedReadBody)))

theorem readSeed_run (C : Ctx) (bits rest : List Bool) (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip = frame bits ++ rest) (hwidth : bits.length < C.Wd) :
    Hs C readSeed a (11 * bits.length + 8) (fun b =>
      b.env t0 = 0 ∧ b.ip = a.ip + (frame bits).length ∧
      b.env seed = prefixValue bits ∧ b.env seedPower = 2 ^ bits.length ∧
      (b.out, b.ram, b.rc, b.kin, b.kout, b.kc) =
        (a.out, a.ram, a.rc, a.kin, a.kout, a.kc) ∧
      Cst b ∧ Fr a b seedReadScratch) := by
  unfold readSeed
  refine (Hs.seq (t2 := 11 * bits.length + 6) (hs_zero C seed a) ?_).mono
    (by omega) (fun _ h => h)
  rintro b rfl
  refine (Hs.seq (t2 := 11 * bits.length + 4) (hs_copy C seedPower v1 _ (by decide)) ?_).mono
    (by omega) (fun _ h => h)
  rintro b rfl
  refine (Hs.seq (t2 := 11 * bits.length + 2)
    (readInputBit_spec C t0 _ (frameFlag bits) (framePayload bits ++ rest)
      (by simpa only [frame_decompose, List.cons_append, DS.set_ip] using hin)) ?_).mono
    (by omega) (fun _ h => h)
  rintro b rfl
  let b : DS VV MM := { (a.set seed 0).set seedPower ((a.set seed 0).env v1) with
    env := Function.update ((a.set seed 0).set seedPower ((a.set seed 0).env v1)).env
      t0 (frameFlag bits).toNat
    ip := a.ip + 1 }
  have hf : Fr a b seedReadScratch :=
    Fr.trans (Fr.set a _ (by simp [seedReadScratch]))
      (Fr.trans (Fr.set _ _ (by simp [seedReadScratch]))
        (Fr.set _ _ (by simp [seedReadScratch])))
  have hbc : Cst b := Cst.of_fr hc hf (by decide)
  have hs : b.env seed = 0 := by
    simp (config := {decide := true}) [b, DS.set]
  have hp : b.env seedPower = 1 := by
    simp (config := {decide := true}) [b, DS.set, hc.one]
  have hnext : C.inp.drop b.ip = framePayload bits ++ rest := by
    change C.inp.drop (a.ip + 1) = _
    rw [← List.drop_drop, hin, frame_decompose]
    rfl
  have hpow : 2 ^ bits.length < 2 ^ C.Wd := Nat.pow_lt_pow_right (by decide) hwidth
  refine (seedReadLoop_run C bits rest b hbc (by simp [b]) hnext
    (by rw [hs, hp, Nat.one_mul, Nat.zero_add]
        exact (Algorithm.CellCall.prefixValue_lt bits).trans hpow)
    (by rw [hp, Nat.one_mul]; exact hpow)).mono le_rfl ?_
  rintro d ⟨hdz, hdi, hds, hdp, hdrest, hdc, hdfr⟩
  refine ⟨hdz, ?_, by simpa [hs, hp] using hds, by simpa [hp] using hdp,
    hdrest, hdc, hf.trans hdfr⟩
  rw [hdi, frame_length]
  change a.ip + 1 + 2 * bits.length = a.ip + (2 * bits.length + 1)
  omega

end NearQuarticWires.StageMain.SampleCells
