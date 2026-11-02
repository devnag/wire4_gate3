import Proof.Quartic.StageMain.CachedTail
import Proof.Quartic.StageMain.SamplePrepare

/-!
# Retained coefficients for the whole sample loop

`imp:seed`, paper/paper.tex, and Step 4 of
`sec:algorithm`: one source scan reads the chosen
seed and the cached modulus. Successive binary divisions retain its
eight coefficients for every sample and certified column.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.Controller

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open SampleCells Algorithm.CellCall

noncomputable def chosenSampleBase (c : Algorithm.CellCall) : SampleRequest where
  ell := c.seed.ell
  modulus := c.seed.modulus
  seed := prefixValue c.chosenSeed
  label := 0
  positive := c.seed.one_le_ell
  modulus_ok := c.seed.cert.2.1
  label_lt := Nat.two_pow_pos _

def prepareCachedTail : St VV MM := .seq scanCachedTail
  (.seq (.op (.zero label)) samplePrepare)

def preparedTailScratch : List (Fin VV) :=
  cachedTailScratch ++ [label] ++ preparationScratch

theorem prepareCachedTail_run (C : Ctx) (c : Algorithm.CellCall) (rest : List Bool)
    (a : DS VV MM) (hc : Cst a) (hell : a.env ell = c.seed.ell)
    (hin : C.inp.drop a.ip = frame (Program.certifiedBits c) ++
      bitWord (Program.consistentBit c) ++ frame c.chosenSeed ++
      binary c.seed.ell c.seed.modulus ++ rest)
    (hW : c.seed.ell + 2 ≤ C.Wd) (hcert : c.ncol < 2 ^ C.Wd)
    (hseed : c.chosenSeed.length < C.Wd) :
    Hs C prepareCachedTail a
      (9 * c.ncol + 11 * c.chosenSeed.length + 15 * c.seed.ell + 154) (fun b =>
      SampleStored (chosenSampleBase c) b ∧
      b.env certifiedCount = c.certifiedColumns.card ∧ b.env columnCounter = c.ncol ∧
      b.env consistency = (Program.consistentBit c).toNat ∧
      b.ip = a.ip + (frame (Program.certifiedBits c)).length +
        (bitWord (Program.consistentBit c)).length + (frame c.chosenSeed).length + c.seed.ell ∧
      (b.out, b.ram, b.rc, b.kin, b.kout, b.kc) =
        (a.out, a.ram, a.rc, a.kin, a.kout, a.kc) ∧ Cst b ∧
      Fr a b preparedTailScratch) := by
  unfold prepareCachedTail
  refine (Hs.seq (t2 := 5 * c.seed.ell + 42)
    (scanCachedTail_run C c rest a hc hell hin hW hcert hseed) ?_).mono
      (by omega) (fun _ h => h)
  rintro b ⟨hbnc, hbncol, hbconsistent, hbseed, _hbpower, hbmod, hbip, hbrest, hbc, hbfr⟩
  refine (Hs.seq (t1 := 1) (t2 := 5 * c.seed.ell + 40) (hs_zero C label b) ?_).mono
    (by omega) (fun _ h => h)
  rintro d rfl
  have hlabel : Fr b (b.set label 0) [label] := Fr.set b _ (by simp)
  have hdc := Cst.of_fr hbc hlabel (by decide)
  refine (samplePrepare_run (chosenSampleBase c) C (b.set label 0) hdc
    (by rw [DS.set_env_ne _ _ (by decide)]; exact hbseed)
    (by rw [DS.set_env_ne _ _ (by decide), hbfr ell (by decide)]; exact hell)
    (by rw [DS.set_env_ne _ _ (by decide)]; exact hbmod)
    (by simp [chosenSampleBase]) hW).mono le_rfl ?_
  rintro e ⟨hestored, hesame, hec, hefr⟩
  refine ⟨hestored, ?_, ?_, ?_, ?_, ?_, hec, ?_⟩
  · rw [hefr certifiedCount (by decide), DS.set_env_ne _ _ (by decide)]
    exact hbnc
  · rw [hefr columnCounter (by decide), DS.set_env_ne _ _ (by decide)]
    exact hbncol
  · rw [hefr consistency (by decide), DS.set_env_ne _ _ (by decide)]
    exact hbconsistent
  · rw [hesame.ip, DS.set_ip, hbip]
  · rw [hesame.out, hesame.ram, hesame.rc, hesame.kin, hesame.kout, hesame.kc]
    exact hbrest
  · exact (hbfr.weaken (by
      intro x hx; simp only [preparedTailScratch, List.mem_append]; tauto)).trans
      ((hlabel.weaken (by
        intro x hx; simp only [preparedTailScratch, List.mem_append]; tauto)).trans
        (hefr.weaken (by
          intro x hx; simp only [preparedTailScratch, List.mem_append]; tauto)))

end NearQuarticWires.StageMain.Controller
