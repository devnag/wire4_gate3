import Proof.Quartic.StageMain.CertifiedScanLoop

/-!
# Exact certificate-frame scanner

Step 4 of `sec:algorithm`, paper/paper.tex: one
streaming pass reaches the seed suffix and records the exact number
of columns and certified columns. Empty frames contribute zero.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.Controller

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open StageLift

def scanCertificate : St VV MM :=
  .seq (.op (.zero certifiedCount)) (.seq (.op (.zero columnCounter))
    (.seq (.op (.rdI t0)) (.loop (.eq t0 v1) countCertificateBody)))

theorem scanCertificate_run (C : Ctx) (bits rest : List Bool) (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip = frame bits ++ rest) (hfit : bits.length < 2 ^ C.Wd) :
    Hs C scanCertificate a (9 * bits.length + 8) (fun b =>
      b.env t0 = 0 ∧ b.ip = a.ip + (frame bits).length ∧
      b.env certifiedCount = trueCount bits ∧ b.env columnCounter = bits.length ∧
      (b.out, b.ram, b.rc, b.kin, b.kout, b.kc) =
        (a.out, a.ram, a.rc, a.kin, a.kout, a.kc) ∧
      Cst b ∧ Fr a b certificateScratch) := by
  unfold scanCertificate
  refine (Hs.seq (t2 := 9 * bits.length + 6) (hs_zero C certifiedCount a) ?_).mono
    (by omega) (fun _ h => h)
  rintro b rfl
  refine (Hs.seq (t2 := 9 * bits.length + 4) (hs_zero C columnCounter _) ?_).mono
    (by omega) (fun _ h => h)
  rintro b rfl
  refine (Hs.seq (t2 := 9 * bits.length + 2)
    (readInputBit_spec C t0 _ (frameFlag bits) (framePayload bits ++ rest)
      (by simpa only [frame_decompose, List.cons_append, DS.set_ip] using hin)) ?_).mono
    (by omega) (fun _ h => h)
  rintro b rfl
  let b : DS VV MM := { (a.set certifiedCount 0).set columnCounter 0 with
    env := Function.update ((a.set certifiedCount 0).set columnCounter 0).env t0
      (frameFlag bits).toNat
    ip := a.ip + 1 }
  have hf : Fr a b certificateScratch :=
    Fr.trans (Fr.set a _ (by simp [certificateScratch]))
      (Fr.trans (Fr.set _ _ (by simp [certificateScratch]))
        (Fr.set _ _ (by simp [certificateScratch])))
  have hbc : Cst b := Cst.of_fr hc hf (by decide)
  have hcnt : b.env certifiedCount = 0 := by
    simp (config := {decide := true}) [b, DS.set]
  have hidx : b.env columnCounter = 0 := by
    simp (config := {decide := true}) [b, DS.set]
  have hnext : C.inp.drop b.ip = framePayload bits ++ rest := by
    change C.inp.drop (a.ip + 1) = _
    rw [← List.drop_drop, hin, frame_decompose]
    rfl
  refine (certificateLoop_run C bits rest b hbc (by simp [b]) hnext
    (by rw [hcnt, Nat.zero_add]; exact (trueCount_le_length bits).trans_lt hfit)
    (by rw [hidx, Nat.zero_add]; exact hfit)).mono le_rfl ?_
  rintro d ⟨hdz, hdi, hdcnt, hdidx, hdrest, hdc, hdfr⟩
  refine ⟨hdz, ?_, by simpa [hcnt] using hdcnt, by simpa [hidx] using hdidx,
    hdrest, hdc, hf.trans hdfr⟩
  rw [hdi, frame_length]
  change a.ip + 1 + 2 * bits.length = a.ip + (2 * bits.length + 1)
  omega

end NearQuarticWires.StageMain.Controller
