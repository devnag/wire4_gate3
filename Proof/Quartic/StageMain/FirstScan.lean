import Proof.Quartic.StageMain.CertifiedScanBuilder
import Proof.Quartic.StageMain.GreedyTail

/-!
# The first streaming pass reaches the chosen seed

Steps 3–4 of `sec:algorithm`, paper/paper.tex:
a single scan of the certificate bitmap records its cardinality and
continues to the consistency flag and chosen seed. No second bitmap
or list of samples is materialized by this pass.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.Controller

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open SampleCells
open Algorithm.CellCall (prefixValue)

def firstScan : St VV MM := .seq scanCertificate readGreedyTail

def firstScanScratch : List (Fin VV) := certificateScratch ++ tailScratch

theorem firstScan_run (C : Ctx) (cert : List Bool) (flag : Bool) (bits rest : List Bool)
    (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip = frame cert ++ bitWord flag ++ frame bits ++ rest)
    (hW : 3 ≤ C.Wd) (hcert : cert.length < 2 ^ C.Wd) (hseed : bits.length < C.Wd) :
    Hs C firstScan a (9 * cert.length + 11 * bits.length + 90) (fun b =>
      b.env certifiedCount = trueCount cert ∧ b.env columnCounter = cert.length ∧
      b.env consistency = flag.toNat ∧ b.env seed = prefixValue bits ∧
      b.env seedPower = 2 ^ bits.length ∧
      b.ip = a.ip + (frame cert).length + (bitWord flag).length + (frame bits).length ∧
      (b.out, b.ram, b.rc, b.kin, b.kout, b.kc) =
        (a.out, a.ram, a.rc, a.kin, a.kout, a.kc) ∧
      Cst b ∧ Fr a b firstScanScratch) := by
  unfold firstScan
  refine (Hs.seq (t2 := 11 * bits.length + 80)
    (scanCertificate_run C cert (bitWord flag ++ frame bits ++ rest) a hc
      (by simpa only [List.append_assoc] using hin) hcert) ?_).mono
      (by omega) (fun _ h => h)
  rintro b ⟨_hbz, hbip, hbcnt, hbidx, hbrest, hbc, hbfr⟩
  have hnext : C.inp.drop b.ip = bitWord flag ++ frame bits ++ rest := by
    rw [hbip, ← List.drop_drop, hin]
    simp only [List.append_assoc, List.drop_left]
  refine (readGreedyTail_run C flag bits rest b hbc hnext hW hseed).mono le_rfl ?_
  rintro d ⟨hdflag, hdseed, hdpower, hdip, hdrest, hdc, hdfr⟩
  exact ⟨(hdfr certifiedCount (by decide)).trans hbcnt,
    (hdfr columnCounter (by decide)).trans hbidx, hdflag, hdseed, hdpower,
    by rw [hdip, hbip], hdrest.trans hbrest, hdc,
    (hbfr.weaken (fun _ hx => List.mem_append_left _ hx)).trans
      (hdfr.weaken (fun _ hx => List.mem_append_right _ hx))⟩

theorem firstScan_call_run (C : Ctx) (c : Algorithm.CellCall) (rest : List Bool)
    (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip = frame (Program.certifiedBits c) ++
      bitWord (Program.consistentBit c) ++ frame c.chosenSeed ++ rest)
    (hW : 3 ≤ C.Wd) (hcert : c.ncol < 2 ^ C.Wd) (hseed : c.chosenSeed.length < C.Wd) :
    Hs C firstScan a (9 * c.ncol + 11 * c.chosenSeed.length + 90) (fun b =>
      b.env certifiedCount = c.certifiedColumns.card ∧ b.env columnCounter = c.ncol ∧
      b.env consistency = (Program.consistentBit c).toNat ∧
      b.env seed = prefixValue c.chosenSeed ∧ b.env seedPower = 2 ^ c.chosenSeed.length ∧
      b.ip = a.ip + (frame (Program.certifiedBits c)).length +
        (bitWord (Program.consistentBit c)).length + (frame c.chosenSeed).length ∧
      (b.out, b.ram, b.rc, b.kin, b.kout, b.kc) =
        (a.out, a.ram, a.rc, a.kin, a.kout, a.kc) ∧
      Cst b ∧ Fr a b firstScanScratch) := by
  have hlen : (Program.certifiedBits c).length = c.ncol := by simp [Program.certifiedBits]
  have h := firstScan_run C (Program.certifiedBits c) (Program.consistentBit c) c.chosenSeed rest
    a hc hin hW (by rw [hlen]; exact hcert) hseed
  rw [trueCount_certifiedBits, hlen] at h
  exact h

end NearQuarticWires.StageMain.Controller
