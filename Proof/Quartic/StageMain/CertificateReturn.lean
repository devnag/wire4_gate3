import Proof.Quartic.StageMain.CachedTailPrepare

/-!
# Paid return to the certificate bitmap

Step 4 of `sec:algorithm`, paper/paper.tex,
returns once from the cached field and chosen seed to the certificate
bitmap. Its distance is `2*ncol + 17*ell + 5`: the bitmap frame,
three-bit consistency word, eight-word seed frame and field cache.
All backward source moves are executed by counted loops.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.Controller

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open SampleCells

def returnScratch : List (Fin VV) := [sampleCounter, vJ]

def retreatBlock (count : Fin VV) : St VV MM := forS sampleCounter count (.op .bkI)

theorem retreatBlock_run (C : Ctx) (count : Fin VV) (hne : sampleCounter ≠ count)
    (N base : ℕ) (a : DS VV MM) (hc : Cst a)
    (hcount : a.env count = N) (hip : a.ip = base + N) (hfit : N < 2 ^ C.Wd) :
    Hs C (retreatBlock count) a (5 * N + 4) (fun b =>
      b.ip = base ∧
      (b.out, b.ram, b.rc, b.kin, b.kout, b.kc) =
        (a.out, a.ram, a.rc, a.kin, a.kout, a.kc) ∧ Cst b ∧ Fr a b returnScratch) := by
  let I : ℕ → DS VV MM → Prop := fun k b => b.ip + k = a.ip ∧
    (b.out, b.ram, b.rc, b.kin, b.kout, b.kc) =
      (a.out, a.ram, a.rc, a.kin, a.kout, a.kc) ∧ Cst b ∧ Fr a b returnScratch
  unfold retreatBlock
  refine (forS_spec' (C := C) sampleCounter count hne (.op .bkI) a N hfit I 1 ?_
    ⟨by omega, rfl, hc, Fr.refl _ _⟩ hcount ?_).mono (by omega) ?_
  · rintro k b value ⟨hbi, hbrest, hbc, hbfr⟩
    have hf : Fr b (b.set sampleCounter value) returnScratch :=
      Fr.set b _ (by simp [returnScratch])
    exact ⟨hbi, hbrest, Cst.of_fr hbc hf (by decide), hbfr.trans hf⟩
  · rintro k hk b ⟨hbi, hbrest, hbc, hbfr⟩ hbk hbn
    refine (Hs.op (OpEx.bkI (C := C) b (by omega)) rfl).mono le_rfl ?_
    rintro d rfl
    exact ⟨⟨by dsimp; omega, hbrest, ⟨hbc.z, hbc.one, hbc.two⟩, hbfr⟩, hbk, hbn⟩
  · rintro b ⟨⟨hbi, hbrest, hbc, hbfr⟩, _, _⟩
    exact ⟨by omega, hbrest, hbc, hbfr⟩

def retreatBlocks (count : Fin VV) : ℕ → St VV MM
  | 0 => skipS
  | k + 1 => .seq (retreatBlock count) (retreatBlocks count k)

theorem retreatBlocks_run (C : Ctx) (count : Fin VV)
    (hne : count ∉ returnScratch) (k N base : ℕ) (a : DS VV MM) (hc : Cst a)
    (hcount : a.env count = N) (hip : a.ip = base + k * N) (hfit : N < 2 ^ C.Wd) :
    Hs C (retreatBlocks count k) a (k * (5 * N + 6) + 1) (fun b =>
      b.ip = base ∧
      (b.out, b.ram, b.rc, b.kin, b.kout, b.kc) =
        (a.out, a.ram, a.rc, a.kin, a.kout, a.kc) ∧ Cst b ∧ Fr a b returnScratch) := by
  have hdistinct : sampleCounter ≠ count := by intro h; exact hne (by simp [returnScratch, ← h])
  induction k generalizing a with
  | zero =>
    refine (skip_spec a).mono (by omega) ?_
    rintro b rfl
    exact ⟨by simpa using hip, rfl,
      Cst.of_fr hc (Fr.set (T := returnScratch) a _ (by simp [returnScratch])) (by decide),
      Fr.set a _ (by simp [returnScratch])⟩
  | succ k ih =>
    unfold retreatBlocks
    refine (Hs.seq (t2 := k * (5 * N + 6) + 1)
      (retreatBlock_run C count hdistinct N (base + k * N) a hc hcount
        (by rw [hip, Nat.succ_mul]; omega) hfit) ?_).mono
        (by simp only [Nat.succ_mul]; omega) (fun _ h => h)
    rintro b ⟨hbip, hbrest, hbc, hbfr⟩
    refine (ih b hbc ((hbfr count hne).trans hcount) hbip).mono le_rfl ?_
    rintro d ⟨hdip, hdrest, hdc, hdfr⟩
    exact ⟨hdip, hdrest.trans hbrest, hdc, hbfr.trans hdfr⟩

def returnToCertificates : St VV MM := .seq (retreatBlocks columnCounter 2)
  (.seq (retreatBlocks ell 17) (retreatBlocks v1 5))

theorem returnToCertificates_run (C : Ctx) (N E base : ℕ) (a : DS VV MM) (hc : Cst a)
    (hN : a.env columnCounter = N) (hE : a.env ell = E)
    (hip : a.ip = base + 2 * N + 17 * E + 5)
    (hNfit : N < 2 ^ C.Wd) (hEfit : E < 2 ^ C.Wd) (h1fit : 1 < 2 ^ C.Wd) :
    Hs C returnToCertificates a (10 * N + 85 * E + 174) (fun b =>
      b.ip = base ∧
      (b.out, b.ram, b.rc, b.kin, b.kout, b.kc) =
        (a.out, a.ram, a.rc, a.kin, a.kout, a.kc) ∧ Cst b ∧ Fr a b returnScratch) := by
  unfold returnToCertificates
  refine (Hs.seq (t2 := 17 * (5 * E + 6) + 1 + 56 + 1)
    (retreatBlocks_run C columnCounter (by decide) 2 N (base + 17 * E + 5) a hc hN
      (by omega) hNfit) ?_).mono (by omega) (fun _ h => h)
  rintro b ⟨hbip, hbrest, hbc, hbfr⟩
  refine Hs.seq (t1 := 17 * (5 * E + 6) + 1) (t2 := 56)
    (retreatBlocks_run C ell (by decide) 17 E (base + 5) b hbc
      ((hbfr ell (by decide)).trans hE) (by omega) hEfit) ?_
  rintro d ⟨hdip, hdrest, hdc, hdfr⟩
  refine (retreatBlocks_run C v1 (by decide) 5 1 base d hdc hdc.one
    (by omega) h1fit).mono le_rfl ?_
  rintro e ⟨heip, herest, hec, hefr⟩
  exact ⟨heip, herest.trans (hdrest.trans hbrest), hec, hbfr.trans (hdfr.trans hefr)⟩

end NearQuarticWires.StageMain.Controller
