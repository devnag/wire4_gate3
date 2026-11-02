import Proof.Quartic.StageMain.CachedTailPrepare
import Proof.Quartic.StageMain.CertificateReturn
import Proof.Quartic.StageMain.ColumnState
import Proof.Quartic.StageMain.CallSizeWords

/-!
# Returning from the seed cache to the actual column bitmap

Step 4 of `sec:algorithm`, paper/paper.tex,
reads the chosen eight-coefficient seed once and then returns the input
head to the certificate bitmap. Every backward input move is charged;
the retained finite source supplies the later sampled entry requests.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.Controller

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open Algorithm Algorithm.CellCall Compact SampleCells

theorem actualChosenSeed_length (c : Algorithm.CellCall) : c.chosenSeed.length = 8 * c.seed.ell := by
  unfold chosenSeed greedySeed
  have h : ∀ j : ℕ, ((greedyStep c.printedPotential)^[j] []).length = j := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      simp [greedyStep, ih]
  exact h _

def prepareSamplePass : St VV MM := .seq prepareCachedTail returnToCertificates

def readyScratch : List (Fin VV) := preparedTailScratch ++ returnScratch

theorem prepareSamplePass_run {B1 B2 : ℕ} (C : Ctx) (c : Call)
    (p : Program.Selected c) (w rest : List Bool) (a : DS VV MM) (hc : Cst a)
    (hell : a.env ell = p.1.ellf) (hQ : a.env sampleLimit = p.1.Q)
    (hkin : a.kin = [])
    (hbits : a.ram compactStore = (Program.prepWord B1 B2 c w).map Bool.toNat)
    (hlen : a.env compactLength = (Program.prepWord B1 B2 c w).length)
    (hcursor : a.rc compactStore = (Program.prepWord B1 B2 c w).length)
    (hin : C.inp.drop a.ip = frame (Program.certifiedBits (Program.runCall c p w)) ++
      bitWord (Program.consistentBit (Program.runCall c p w)) ++ frame (Program.runCall c p w).chosenSeed ++
      binary p.1.ellf (Program.runCall c p w).seed.modulus ++ rest)
    (hW : p.1.ellf + 2 ≤ C.Wd) (hcert : 2 ^ (c.n - p.1.k) < 2 ^ C.Wd)
    (hseed : 8 * p.1.ellf < C.Wd)
    (hEfit : p.1.ellf < 2 ^ C.Wd) (h1fit : 1 < 2 ^ C.Wd) :
    Hs C prepareSamplePass a (19 * 2 ^ (c.n - p.1.k) + 188 * p.1.ellf + 329) (fun b =>
      MainRetained B1 B2 c p w b ∧
      b.env certifiedCount = (Program.runCall c p w).certifiedColumns.card ∧
      b.env columnCounter = 2 ^ (c.n - p.1.k) ∧
      b.env consistency = (Program.consistentBit (Program.runCall c p w)).toNat ∧
      b.ip = a.ip ∧ (b.out, b.ram, b.rc, b.kin, b.kout, b.kc) =
        (a.out, a.ram, a.rc, a.kin, a.kout, a.kc) ∧ Cst b ∧ Fr a b readyScratch) := by
  let cc := Program.runCall c p w
  have hlength : cc.chosenSeed.length = 8 * p.1.ellf := actualChosenSeed_length cc
  have ht := prepareCachedTail_run C cc rest a hc hell hin hW hcert (by rw [hlength]; exact hseed)
  rw [hlength] at ht
  unfold prepareSamplePass
  refine (Hs.seq (t2 := 10 * 2 ^ (c.n - p.1.k) + 85 * p.1.ellf + 174) ht ?_).mono
    (by change 9 * 2 ^ (c.n - p.1.k) + 11 * (8 * p.1.ellf) + 15 * p.1.ellf + 154 + _ + 1 ≤ _; omega)
    (fun _ h => h)
  rintro b ⟨hstored, hbnc, hbN, hbcon, hbip, hbrest, hbc, hbfr⟩
  have hbpos : b.ip = a.ip + 2 * 2 ^ (c.n - p.1.k) + 17 * p.1.ellf + 5 := by
    rw [frame_length, frame_length, CallSize.bitWord_length, hlength] at hbip
    simp only [Program.certifiedBits, List.length_ofFn] at hbip
    change b.ip = a.ip + (2 * 2 ^ (c.n - p.1.k) + 1) + 3 + (2 * (8 * p.1.ellf) + 1) + p.1.ellf at hbip
    omega
  refine (returnToCertificates_run C (2 ^ (c.n - p.1.k)) p.1.ellf a.ip b hbc hbN
    hstored.degree hbpos hcert hEfit h1fit).mono le_rfl ?_
  rintro d ⟨hdip, hdrest, hdc, hdfr⟩
  have hrest := hdrest.trans hbrest
  rcases (by simpa only [Prod.mk.injEq] using hrest) with ⟨hdo, hdram, hdrc, hdkin, _hdkout, _hdkc⟩
  have hframes : Fr a d readyScratch :=
    (hbfr.weaken (fun _ hx => List.mem_append_left _ hx)).trans
      (hdfr.weaken (fun _ hx => List.mem_append_right _ hx))
  refine ⟨⟨⟨(hdfr ell (by decide)).trans hstored.degree,
    (hdfr modulus (by decide)).trans hstored.field, ?_⟩,
    hdkin.trans hkin, by rw [hdram]; exact hbits,
    (hframes compactLength (by decide)).trans hlen, by rw [hdrc]; exact hcursor,
    (hframes sampleLimit (by decide)).trans hQ⟩,
    (hdfr certifiedCount (by decide)).trans hbnc,
    (hdfr columnCounter (by decide)).trans hbN,
    (hdfr consistency (by decide)).trans hbcon, hdip, hrest, hdc, hframes⟩
  intro i
  have hi : coefficient i ∉ returnScratch := by fin_cases i <;> decide
  exact (hdfr _ hi).trans (hstored.coeff i)

end NearQuarticWires.StageMain.Controller
