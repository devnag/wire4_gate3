import Proof.Quartic.StageMain.EntrySample
import Proof.Quartic.StageMain.SampleSums

/-!
# The counted loop over the chosen-seed samples

Step 4 of `sec:algorithm`, paper/paper.tex,
evaluates all `Q` labels with the same retained coefficients. The
loop invariant records the two exact prefix sums, retains the finite
source and leaves the certificate cursor at its current column.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.Controller

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open Compact SampleCells Algorithm.CellCall

def sampleLimit : Fin VV := 98

def sampleLoop : St VV MM := forS label sampleLimit sampledEntryStep

def sampleLoopScratch : List (Fin VV) := label :: sampledEntryScratch

structure SeedCoefficients (c : Algorithm.CellCall) (a : DS VV MM) : Prop where
  degree : a.env ell = c.seed.ell
  field : a.env modulus = c.seed.modulus
  coeff : ∀ i, a.env (coefficient i) = Sampler.seedCoeff c.seed.ell (prefixValue c.chosenSeed) i

theorem SeedCoefficients.frame {c : Algorithm.CellCall} {a b : DS VV MM}
    (h : SeedCoefficients c a) (hf : Fr a b sampleLoopScratch) : SeedCoefficients c b := by
  refine ⟨(hf ell (by decide)).trans h.degree, (hf modulus (by decide)).trans h.field, ?_⟩
  intro i
  have hi : coefficient i ∉ sampleLoopScratch := by fin_cases i <;> decide
  exact (hf _ hi).trans (h.coeff i)

theorem SeedCoefficients.stored {c : Algorithm.CellCall} {a : DS VV MM}
    (h : SeedCoefficients c a) (j : Fin c.seed.Q) (hj : a.env label = j.val) :
    SampleStored (actualSampleRequest c.seed (prefixValue c.chosenSeed) j) a :=
  ⟨h.degree, h.field, hj, h.coeff⟩

variable {B1 B2 : ℕ} {budget : EntryRequest B1 B2 → ℕ}

theorem sampleLoop_run
    (f : WordFunction (EntryRequest B1 B2) entryWord entryOutput budget)
    {c : Call} {p : Program.Selected c} (hd : Program.dispatch B1 B2 c = some p)
    (w : List Bool) (z : Fin (2 ^ (c.n - p.1.k)))
    (width : ℕ) (input : List Bool) (L B T : ℕ) (a : DS VV MM) (hc : Cst a)
    (hs : SeedCoefficients (Program.runCall c p w) a) (hkin : a.kin = [])
    (hbits : a.ram compactStore = (Program.prepWord B1 B2 c w).map Bool.toNat)
    (hlen : a.env compactLength = (Program.prepWord B1 B2 c w).length)
    (hcursor : a.rc compactStore = (Program.prepWord B1 B2 c w).length)
    (hcol : a.env columnCounter = z.val) (hQ : a.env sampleLimit = p.1.Q)
    (hW : p.1.ellf + 2 ≤ width) (hQfit : p.1.Q < 2 ^ width)
    (hfit : (Program.prepWord B1 B2 c w).length < 2 ^ width)
    (hcolfit : natBitLength z.val + 2 < 2 ^ width)
    (hvaluefit : ∀ j : Fin p.1.Q,
      natBitLength (sampledEntryRequest hd w z j).fieldValue.val + 2 < 2 ^ width)
    (hSL : 10000 * (p.1.ellf + 1) + 1 ≤ L)
    (hSB : 30000000 * (p.1.ellf + 1) ^ 2 ≤ B)
    (hEL : ∀ j : Fin p.1.Q, 1 + (entryWord (sampledEntryRequest hd w z j)).length ≤ L)
    (hEB : ∀ j : Fin p.1.Q, (sampleTaggedCallee f).bud (.inr (sampledEntryRequest hd w z j)) ≤ B)
    (hT : ∀ j : Fin p.1.Q,
      9 * (Program.prepWord B1 B2 c w).length + 40 * natBitLength z.val +
        40 * natBitLength (sampledEntryRequest hd w z j).fieldValue.val +
        3 * L + 2 * B + 12 * p.1.ellf + 150 ≤ T)
    (hA : a.env acceptanceTotal + p.1.Q < 2 ^ width)
    (hM : a.env maskTotal + p.1.Q < 2 ^ width) :
    Hs (taggedContext width input f L B) sampleLoop a (p.1.Q * (T + 4) + 4) (fun b =>
      b.env acceptanceTotal = a.env acceptanceTotal + sampleAcceptancePrefix (Program.runCall c p w) z p.1.Q ∧
      b.env maskTotal = a.env maskTotal + sampleMaskPrefix (Program.runCall c p w) z p.1.Q ∧
      b.env label = p.1.Q ∧ b.env sampleLimit = p.1.Q ∧
      b.kin = [] ∧ b.ip = a.ip ∧ b.out = a.out ∧ b.ram = a.ram ∧ b.rc = a.rc ∧
      Cst b ∧ Fr a b sampleLoopScratch) := by
  let C := taggedContext width input f L B
  let cc := Program.runCall c p w
  let I : ℕ → DS VV MM → Prop := fun k b =>
    SeedCoefficients cc b ∧
    b.env acceptanceTotal = a.env acceptanceTotal + sampleAcceptancePrefix cc z k ∧
    b.env maskTotal = a.env maskTotal + sampleMaskPrefix cc z k ∧
    b.kin = [] ∧ b.ip = a.ip ∧ b.out = a.out ∧ b.ram = a.ram ∧ b.rc = a.rc ∧
    Cst b ∧ Fr a b sampleLoopScratch
  have hI : ∀ k b value, I k b → I k (b.set label value) := by
    rintro k b value ⟨hbs, hbA, hbM, hbk, hbi, hbo, hbr, hbrc, hbc, hbf⟩
    have hf : Fr b (b.set label value) sampleLoopScratch := Fr.set b _ (by simp [sampleLoopScratch])
    exact ⟨hbs.frame hf, by rw [DS.set_env_ne _ _ (by decide)]; exact hbA,
      by rw [DS.set_env_ne _ _ (by decide)]; exact hbM,
      hbk, hbi, hbo, hbr, hbrc, Cst.of_fr hbc hf (by decide), hbf.trans hf⟩
  have h0 : I 0 a := ⟨hs, by simp [sampleAcceptancePrefix], by simp [sampleMaskPrefix],
    hkin, rfl, rfl, rfl, rfl, hc, Fr.refl _ _⟩
  unfold sampleLoop
  refine (forS_spec' (C := C) label sampleLimit (by decide) sampledEntryStep a p.1.Q hQfit
    I T hI h0 hQ ?_).mono le_rfl ?_
  · rintro k hk b ⟨hbs, hbA, hbM, hbkin, hbip, hbo, hbr, hbrc, hbc, hbfr⟩ hbk hbQ
    let j : Fin p.1.Q := ⟨k, hk⟩
    have hhA := sampleAcceptancePrefix_le cc z k
    have hhM := sampleMaskPrefix_le cc z k
    have hrun := sampledEntryStep_run f hd w z j width input L B b hbc
      (hbs.stored j hbk) hbkin ((congrFun hbr compactStore).trans hbits)
      ((hbfr compactLength (by decide)).trans hlen)
      (by rw [hbrc]; exact hcursor) ((hbfr columnCounter (by decide)).trans hcol)
      hW hfit hcolfit (hvaluefit j) hSL hSB (hEL j) (hEB j)
      (by rw [hbA]; omega) (by rw [hbM]; omega)
    refine hrun.mono (hT j) ?_
    rintro d ⟨hdA, hdM, hdk, hdi, hdo, hdr, hdrc, hdc, hdfr⟩
    have hdf : Fr b d sampleLoopScratch := hdfr.weaken (fun _ hx => List.mem_cons_of_mem _ hx)
    refine ⟨⟨hbs.frame hdf, ?_, ?_, hdk, hdi.trans hbip, hdo.trans hbo,
      hdr.trans hbr, hdrc.trans hbrc, hdc, hbfr.trans hdf⟩,
      (hdfr label (by decide)).trans hbk, (hdfr sampleLimit (by decide)).trans hbQ⟩
    · rw [hdA, hbA, sampledEntry_acceptance]
      rw [sampleAcceptancePrefix_succ]
      exact Nat.add_assoc _ _ _
    · rw [hdM, hbM, sampledEntry_maskNat]
      rw [sampleMaskPrefix_succ]
      exact Nat.add_assoc _ _ _
  · rintro b ⟨⟨_hs, hbA, hbM, hbk, hbi, hbo, hbr, hbrc, hbc, hbf⟩, hbl, hbQ⟩
    exact ⟨hbA, hbM, hbl, hbQ, hbk, hbi, hbo, hbr, hbrc, hbc, hbf⟩

end NearQuarticWires.StageMain.Controller
