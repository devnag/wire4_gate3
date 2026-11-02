import Proof.Quartic.StageMain.EntryCall
import Proof.Quartic.StageMain.SampleTaggedStep

/-!
# One sampled contribution to both main-pass totals

Step 4 of `sec:algorithm`, paper/paper.tex:
the actual Horner sampler determines the field value, the numeric
entry machine evaluates its predicate and mask, and the two Boolean
contributions are added to the retained totals.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.Controller

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open Compact SampleCells

variable {B1 B2 : ℕ} {budget : EntryRequest B1 B2 → ℕ}

def sampledEntryStep : St VV MM := .seq taggedSampleStep (.seq callEntry addSample)

def sampledEntryScratch : List (Fin VV) :=
  cachedSampleScratch ++ entryCallScratch ++ totalsScratch

theorem sampledEntryStep_run
    (f : WordFunction (EntryRequest B1 B2) entryWord entryOutput budget)
    {c : Call} {p : Program.Selected c} (hd : Program.dispatch B1 B2 c = some p)
    (w : List Bool) (z : Fin (2 ^ (c.n - p.1.k))) (j : Fin p.1.Q)
    (width : ℕ) (input : List Bool) (L B : ℕ) (a : DS VV MM) (hc : Cst a)
    (hs : SampleStored (actualSampleRequest (Program.runCall c p w).seed
      (Algorithm.CellCall.prefixValue (Program.runCall c p w).chosenSeed) j) a)
    (hkin : a.kin = [])
    (hbits : a.ram compactStore = (Program.prepWord B1 B2 c w).map Bool.toNat)
    (hlen : a.env compactLength = (Program.prepWord B1 B2 c w).length)
    (hcursor : a.rc compactStore = (Program.prepWord B1 B2 c w).length)
    (hcol : a.env columnCounter = z.val)
    (hW : p.1.ellf + 2 ≤ width)
    (hfit : (Program.prepWord B1 B2 c w).length < 2 ^ width)
    (hcolfit : natBitLength z.val + 2 < 2 ^ width)
    (hvaluefit : natBitLength (sampledEntryRequest hd w z j).fieldValue.val + 2 < 2 ^ width)
    (hSL : 10000 * (p.1.ellf + 1) + 1 ≤ L)
    (hSB : 30000000 * (p.1.ellf + 1) ^ 2 ≤ B)
    (hEL : 1 + (entryWord (sampledEntryRequest hd w z j)).length ≤ L)
    (hEB : (sampleTaggedCallee f).bud (.inr (sampledEntryRequest hd w z j)) ≤ B)
    (hA : a.env acceptanceTotal + 1 < 2 ^ width)
    (hM : a.env maskTotal + 1 < 2 ^ width) :
    Hs (taggedContext width input f L B) sampledEntryStep a
      (9 * (Program.prepWord B1 B2 c w).length + 40 * natBitLength z.val +
        40 * natBitLength (sampledEntryRequest hd w z j).fieldValue.val +
        3 * L + 2 * B + 12 * p.1.ellf + 150) (fun b =>
      b.env acceptanceTotal = a.env acceptanceTotal +
        (entryPredicate (sampledEntryRequest hd w z j) && entryMask (sampledEntryRequest hd w z j)).toNat ∧
      b.env maskTotal = a.env maskTotal + (entryMask (sampledEntryRequest hd w z j)).toNat ∧
      b.kin = [] ∧ b.ip = a.ip ∧ b.out = a.out ∧ b.ram = a.ram ∧ b.rc = a.rc ∧
      Cst b ∧ Fr a b sampledEntryScratch) := by
  let C := taggedContext width input f L B
  let r := sampledEntryRequest hd w z j
  have hell : (Program.runCall c p w).seed.ell = p.1.ellf := rfl
  unfold sampledEntryStep
  refine (Hs.seq
    (t2 := 9 * (Program.prepWord B1 B2 c w).length + 40 * natBitLength z.val +
      40 * natBitLength r.fieldValue.val + L + B + 116)
    (taggedSampleStep_run f _ width input L B a hc hs hkin hW hSL hSB) ?_).mono
      (by dsimp only [r, actualSampleRequest]; rw [hell]; omega) (fun _ h => h)
  rintro b ⟨hbv, _hbkc, _hbkout, hbkin, hbip, hbo, hbr, hbrc, hbc, hbfr⟩
  refine (Hs.seq (t2 := 5)
    (callEntry_run f r width input L B b hbc hbkin
      ((congrFun hbr compactStore).trans hbits) ((hbfr compactLength (by decide)).trans hlen)
      (by rw [hbrc]; exact hcursor) ((hbfr columnCounter (by decide)).trans hcol)
      hbv (by omega) hfit hcolfit hvaluefit hEL hEB) ?_).mono (by dsimp only [r, sampledEntryRequest]; omega) (fun _ h => h)
  rintro d ⟨hdp, hdm, hdkin, _hdkout, _hdkc, hdip, hdo, hdr, hdrc, hdc, hdfr⟩
  have hdA : d.env acceptanceTotal = a.env acceptanceTotal :=
    (hdfr acceptanceTotal (by decide)).trans (hbfr acceptanceTotal (by decide))
  have hdM : d.env maskTotal = a.env maskTotal :=
    (hdfr maskTotal (by decide)).trans (hbfr maskTotal (by decide))
  refine (addSample_run C d hdc (entryPredicate r) (entryMask r) hdp hdm
    (by rw [hdA]; exact hA) (by rw [hdM]; exact hM)).mono le_rfl ?_
  rintro e ⟨heA, heM, hesame, hec, hefr⟩
  refine ⟨by rw [heA, hdA], by rw [heM, hdM], hesame.kin.trans hdkin,
    hesame.ip.trans (hdip.trans hbip), hesame.out.trans (hdo.trans hbo),
    hesame.ram.trans (hdr.trans hbr), hesame.rc.trans (hdrc.trans hbrc), hec, ?_⟩
  exact (hbfr.weaken (by
    intro x hx; simp only [sampledEntryScratch, List.mem_append]; tauto)).trans
    ((hdfr.weaken (by
      intro x hx; simp only [sampledEntryScratch, List.mem_append]; tauto)).trans
      (hefr.weaken (by
        intro x hx; simp only [sampledEntryScratch, List.mem_append]; tauto)))

end NearQuarticWires.StageMain.Controller
