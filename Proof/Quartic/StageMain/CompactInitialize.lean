import Proof.Quartic.StageMain.CompactDecode
import Proof.Quartic.StageMain.CompactRewind

/-!
# Initialization before the certificate scan

Step 4 of `sec:algorithm`, paper/paper.tex:
the original source is retained and decoded with two finite-prefix
passes. Its certificate bitmap remains a stream, while the original
call, parameters and witness are available for every sample.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.Compact

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open StageLift

def initializeCompact : St VV MM := .seq acquireCompact (.seq rewindCompact decodeCompact)

def initializeCost (c : Call) (p : Cells.Parameters) (witness : List Bool) (B : ℕ) : ℕ :=
  acquireCost c p witness + 5 * (compactInput c p witness).length + decodeCost c p witness B + 8

def initializeScratch : List (Fin VV) := acquireScratch ++
  [StageRecovery.tokenLengthVar, StageRecovery.inputReturnIndex] ++ decodeScratch

theorem initialize_run (C : Ctx) (c : Call) (p : Cells.Parameters) (B : ℕ)
    (witness rest : List Bool) (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip = compactInput c p witness ++ rest)
    (hW : (preparedPrefixWord c p).length + 2 ≤ C.Wd)
    (hcap : (compactInput c p witness).length < 2 ^ C.Wd)
    (hwidth : ∀ value ∈ parameterHeadFields p ++ p.primes.sort (· ≤ ·) ++
      parameterTailFields p ++ p.factors, natBitLength value ≤ B)
    (hB : B + 2 ≤ C.Wd)
    (hcounts : p.primes.card < 2 ^ C.Wd ∧ p.factors.length < 2 ^ C.Wd)
    (hempty : ∀ store ∈ compactStore :: decodeStores, a.ram store = [] ∧ a.rc store = 0) :
    Hs C initializeCompact a (initializeCost c p witness B) (fun b =>
      b.ip = a.ip + (compactInput c p witness).length ∧ Decoded c p witness b ∧
      b.env compactLength = (compactInput c p witness).length ∧
      b.ram compactStore = (compactInput c p witness).map Bool.toNat ∧
      b.rc compactStore = (compactInput c p witness).length ∧
      (b.out, b.kin, b.kout, b.kc) = (a.out, a.kin, a.kout, a.kc) ∧
      Cst b ∧ Fr a b initializeScratch) := by
  unfold initializeCompact
  refine (Hs.seq
    (t2 := 5 * (compactInput c p witness).length + decodeCost c p witness B + 7)
    (acquireCompact_run C c p witness rest a hc hin hW hcap (hempty _ (by simp))) ?_).mono
      (by unfold initializeCost; omega) (fun _ h => h)
  rintro b ⟨hbip, hblen, _hbbytes, hbram, hbrc, hbother, hbrest, hbc, hbfr⟩
  refine (Hs.seq (t2 := decodeCost c p witness B)
    (rewindCompact_run C a.ip (compactInput c p witness).length b hbc hbip hblen hcap) ?_).mono
      (by omega) (fun _ h => h)
  rintro d ⟨hdip, hdrest, hdc, hdfr⟩
  have hdram : d.ram = b.ram := congrArg (fun t => t.2.1) hdrest
  have hdrc : d.rc = b.rc := congrArg (fun t => t.2.2.1) hdrest
  have hdsmall : (d.out, d.kin, d.kout, d.kc) = (b.out, b.kin, b.kout, b.kc) :=
    congrArg (fun t => (t.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2)) hdrest
  have hdempty : ∀ store ∈ decodeStores, d.ram store = [] ∧ d.rc store = 0 := by
    intro store hs
    have hne : store ≠ compactStore := by
      rcases (by simpa only [decodeStores, List.mem_cons, List.not_mem_nil, or_false] using hs) with
        hs | hs | hs | hs | hs <;> subst store <;> decide
    obtain ⟨hr, hrc⟩ := hbother store hne
    rw [hdram, hdrc, hr, hrc]
    exact hempty store (List.mem_cons_of_mem _ hs)
  refine (decodeCompact_run C c p B witness rest d hdc (by rw [hdip]; exact hin)
    (by simp only [preparedPrefixWord, List.length_cons, List.length_append] at hW; omega)
    hwidth hB hcounts hdempty).mono le_rfl ?_
  rintro e ⟨heip, hedata, heother, herest, hec, hefr⟩
  refine ⟨by rw [heip, hdip], hedata, ?_, ?_, ?_, herest.trans (hdsmall.trans hbrest), hec, ?_⟩
  · rw [hefr _ (by decide), hdfr _ (by decide), hblen]
  · rw [(heother compactStore (by decide)).1, hdram, hbram]
  · rw [(heother compactStore (by decide)).2, hdrc, hbrc]
  · exact (hbfr.weaken (by intro x hx; simp only [initializeScratch, List.mem_append]; tauto)).trans
      ((hdfr.weaken (by intro x hx; simp only [initializeScratch, List.mem_append]; tauto)).trans
        (hefr.weaken (by intro x hx; simp only [initializeScratch, List.mem_append]; tauto)))

end NearQuarticWires.StageMain.Compact
