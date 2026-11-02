import Proof.Quartic.StageMain.FirstScan
import Proof.Quartic.StageMain.FieldCacheRead

/-!
# One certificate scan followed by the computed field cache

Step 4 of `sec:algorithm`, paper/paper.tex,
reads the certified-column bitmap, the consistency flag and the
chosen seed. The cache from `imp:seed`, supplies the
primitive polynomial without recomputing it for a sample.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.Controller

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open SampleCells Algorithm.CellCall

def scanCachedTail : St VV MM := .seq firstScan readFieldCache

def cachedTailScratch : List (Fin VV) :=
  firstScanScratch ++ StageGamma.fixedReadScratch modulus

theorem scanCachedTail_run (C : Ctx) (c : Algorithm.CellCall) (rest : List Bool)
    (a : DS VV MM) (hc : Cst a) (hell : a.env ell = c.seed.ell)
    (hin : C.inp.drop a.ip = frame (Program.certifiedBits c) ++
      bitWord (Program.consistentBit c) ++ frame c.chosenSeed ++
      binary c.seed.ell c.seed.modulus ++ rest)
    (hW : c.seed.ell + 2 ≤ C.Wd) (hcert : c.ncol < 2 ^ C.Wd)
    (hseed : c.chosenSeed.length < C.Wd) :
    Hs C scanCachedTail a
      (9 * c.ncol + 11 * c.chosenSeed.length + 10 * c.seed.ell + 111) (fun b =>
      b.env certifiedCount = c.certifiedColumns.card ∧ b.env columnCounter = c.ncol ∧
      b.env consistency = (Program.consistentBit c).toNat ∧
      b.env seed = prefixValue c.chosenSeed ∧ b.env seedPower = 2 ^ c.chosenSeed.length ∧
      b.env modulus = c.seed.modulus ∧
      b.ip = a.ip + (frame (Program.certifiedBits c)).length +
        (bitWord (Program.consistentBit c)).length + (frame c.chosenSeed).length + c.seed.ell ∧
      (b.out, b.ram, b.rc, b.kin, b.kout, b.kc) =
        (a.out, a.ram, a.rc, a.kin, a.kout, a.kc) ∧ Cst b ∧
      Fr a b cachedTailScratch) := by
  have hthree : 3 ≤ C.Wd := by have := c.seed.one_le_ell; omega
  unfold scanCachedTail
  refine (Hs.seq (t2 := 10 * c.seed.ell + 20)
    (firstScan_call_run C c (binary c.seed.ell c.seed.modulus ++ rest) a hc
      (by simpa only [List.append_assoc] using hin) hthree hcert hseed) ?_).mono
      (by omega) (fun _ h => h)
  rintro b ⟨hbnc, hbncol, hbconsistent, hbseed, hbpower, hbip, hbrest, hbc, hbfr⟩
  have hnext : C.inp.drop b.ip = binary c.seed.ell c.seed.modulus ++ rest := by
    rw [hbip, ← List.drop_drop, ← List.drop_drop, ← List.drop_drop, hin]
    simp only [List.append_assoc, List.drop_left]
  refine (readFieldCache_run C c.seed.ell c.seed.modulus c.seed.cert.2.1 rest b hbc
    ((hbfr ell (by decide)).trans hell) hW hnext).mono le_rfl ?_
  rintro d ⟨hdmod, hdip, hdrest, hdc, hdfr⟩
  exact ⟨(hdfr certifiedCount (by decide)).trans hbnc,
    (hdfr columnCounter (by decide)).trans hbncol,
    (hdfr consistency (by decide)).trans hbconsistent,
    (hdfr seed (by decide)).trans hbseed,
    (hdfr seedPower (by decide)).trans hbpower, hdmod,
    by rw [hdip, hbip], hdrest.trans hbrest, hdc,
    (hbfr.weaken (fun _ hx => List.mem_append_left _ hx)).trans
      (hdfr.weaken (fun _ hx => List.mem_append_right _ hx))⟩

end NearQuarticWires.StageMain.Controller
