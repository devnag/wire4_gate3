import Proof.Quartic.StageMain.CertifiedScan
import Proof.Quartic.Program.Stages

/-!
# Certified-column count from the literal stage bitmap

Step 4 of `sec:algorithm`, paper/paper.tex: the
streamed true-flag count is exactly the cardinality of the certified
column set used in the output interval.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.Controller

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells

theorem trueCount_certifiedBits (C : Algorithm.CellCall) :
    trueCount (Program.certifiedBits C) = C.certifiedColumns.card := by
  classical
  simp [trueCount, Program.certifiedBits, List.map_ofFn, List.sum_ofFn, Bool.toNat, Bool.cond_decide]

theorem scanCertifiedColumns_run (C : Ctx) (c : Algorithm.CellCall) (rest : List Bool)
    (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip = frame (Program.certifiedBits c) ++ rest)
    (hfit : c.ncol < 2 ^ C.Wd) :
    Hs C scanCertificate a (9 * c.ncol + 8) (fun b =>
      b.env t0 = 0 ∧ b.ip = a.ip + 2 * c.ncol + 1 ∧
      b.env certifiedCount = c.certifiedColumns.card ∧ b.env columnCounter = c.ncol ∧
      (b.out, b.ram, b.rc, b.kin, b.kout, b.kc) =
        (a.out, a.ram, a.rc, a.kin, a.kout, a.kc) ∧
      Cst b ∧ Fr a b certificateScratch) := by
  classical
  have hlen : (Program.certifiedBits c).length = c.ncol := by
    simp [Program.certifiedBits]
  have h := scanCertificate_run C (Program.certifiedBits c) rest a hc hin
    (by rw [hlen]; exact hfit)
  rw [trueCount_certifiedBits] at h
  simpa only [frame_length, hlen, Nat.add_assoc] using h

end NearQuarticWires.StageMain.Controller
