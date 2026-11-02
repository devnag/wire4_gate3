import Proof.Quartic.StageMain.SampleLoop
import Proof.Quartic.StageMain.ColumnFlag

/-!
# Retained source and arithmetic bounds for the column stream

Step 4 of `sec:algorithm`, paper/paper.tex,
keeps the original finite source and eight seed coefficients across
all columns. The bounds below state the actual binary capacities
and ordinary call reservations used by the fixed sample program.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.Controller

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open Compact SampleCells

def columnBodyScratch : List (Fin VV) := columnFlagScratch ++ sampleLoopScratch

def columnScratch : List (Fin VV) := columnCounter :: columnBodyScratch

def columnLimit : Fin VV := 99

structure MainRetained (B1 B2 : ℕ) (c : Call) (p : Program.Selected c)
    (w : List Bool) (a : DS VV MM) : Prop where
  coefficients : SeedCoefficients (Program.runCall c p w) a
  kin : a.kin = []
  bits : a.ram compactStore = (Program.prepWord B1 B2 c w).map Bool.toNat
  length : a.env compactLength = (Program.prepWord B1 B2 c w).length
  cursor : a.rc compactStore = (Program.prepWord B1 B2 c w).length
  samples : a.env sampleLimit = p.1.Q

theorem MainRetained.frame {B1 B2 : ℕ} {c : Call} {p : Program.Selected c}
    {w : List Bool} {a b : DS VV MM} (h : MainRetained B1 B2 c p w a)
    (hkin : b.kin = []) (hram : b.ram = a.ram) (hrc : b.rc = a.rc)
    (hf : Fr a b columnScratch) : MainRetained B1 B2 c p w b := by
  refine ⟨⟨(hf ell (by decide)).trans h.coefficients.degree,
    (hf modulus (by decide)).trans h.coefficients.field, ?_⟩,
    hkin, (congrFun hram compactStore).trans h.bits,
    (hf compactLength (by decide)).trans h.length,
    (congrFun hrc compactStore).trans h.cursor,
    (hf sampleLimit (by decide)).trans h.samples⟩
  intro i
  have hi : coefficient i ∉ columnScratch := by fin_cases i <;> decide
  exact (hf _ hi).trans (h.coefficients.coeff i)

structure SamplingBounds {B1 B2 : ℕ} {budget : EntryRequest B1 B2 → ℕ}
    (f : WordFunction (EntryRequest B1 B2) entryWord entryOutput budget)
    {c : Call} {p : Program.Selected c} (hd : Program.dispatch B1 B2 c = some p)
    (w : List Bool) (width L B T : ℕ) : Prop where
  widthOk : p.1.ellf + 2 ≤ width
  samples : p.1.Q < 2 ^ width
  compact : (Program.prepWord B1 B2 c w).length < 2 ^ width
  column : ∀ z : Fin (2 ^ (c.n - p.1.k)), natBitLength z.val + 2 < 2 ^ width
  value : ∀ (z : Fin (2 ^ (c.n - p.1.k))) (j : Fin p.1.Q),
    natBitLength (sampledEntryRequest hd w z j).fieldValue.val + 2 < 2 ^ width
  samplerInput : 10000 * (p.1.ellf + 1) + 1 ≤ L
  samplerClock : 30000000 * (p.1.ellf + 1) ^ 2 ≤ B
  entryInput : ∀ (z : Fin (2 ^ (c.n - p.1.k))) (j : Fin p.1.Q),
    1 + (entryWord (sampledEntryRequest hd w z j)).length ≤ L
  entryClock : ∀ (z : Fin (2 ^ (c.n - p.1.k))) (j : Fin p.1.Q),
    (sampleTaggedCallee f).bud (.inr (sampledEntryRequest hd w z j)) ≤ B
  stepClock : ∀ (z : Fin (2 ^ (c.n - p.1.k))) (j : Fin p.1.Q),
    9 * (Program.prepWord B1 B2 c w).length + 40 * natBitLength z.val +
      40 * natBitLength (sampledEntryRequest hd w z j).fieldValue.val +
      3 * L + 2 * B + 12 * p.1.ellf + 150 ≤ T

theorem sampleLoop_retained {B1 B2 : ℕ} {budget : EntryRequest B1 B2 → ℕ}
    (f : WordFunction (EntryRequest B1 B2) entryWord entryOutput budget)
    {c : Call} {p : Program.Selected c} (hd : Program.dispatch B1 B2 c = some p)
    (w : List Bool) (z : Fin (2 ^ (c.n - p.1.k)))
    (width : ℕ) (input : List Bool) (L B T : ℕ) (h : SamplingBounds f hd w width L B T)
    (a : DS VV MM) (hc : Cst a) (hr : MainRetained B1 B2 c p w a)
    (hcol : a.env columnCounter = z.val)
    (hA : a.env acceptanceTotal + p.1.Q < 2 ^ width)
    (hM : a.env maskTotal + p.1.Q < 2 ^ width) :
    Hs (taggedContext width input f L B) sampleLoop a (p.1.Q * (T + 4) + 4) (fun b =>
      b.env acceptanceTotal = a.env acceptanceTotal + sampleAcceptancePrefix (Program.runCall c p w) z p.1.Q ∧
      b.env maskTotal = a.env maskTotal + sampleMaskPrefix (Program.runCall c p w) z p.1.Q ∧
      MainRetained B1 B2 c p w b ∧ b.ip = a.ip ∧ b.out = a.out ∧ b.ram = a.ram ∧
      b.rc = a.rc ∧ Cst b ∧ Fr a b sampleLoopScratch) := by
  refine (sampleLoop_run f hd w z width input L B T a hc hr.coefficients hr.kin hr.bits hr.length
    hr.cursor hcol hr.samples h.widthOk h.samples h.compact (h.column z) (h.value z)
    h.samplerInput h.samplerClock (h.entryInput z) (h.entryClock z) (h.stepClock z) hA hM).mono le_rfl ?_
  rintro b ⟨hbA, hbM, _hblabel, _hbQ, hbkin, hbip, hbo, hbr, hbrc, hbc, hbfr⟩
  have hf : Fr a b columnScratch := hbfr.weaken (by
    intro x hx; simp only [columnScratch, columnBodyScratch, List.mem_cons, List.mem_append]; tauto)
  exact ⟨hbA, hbM, hr.frame hbkin hbr hbrc hf, hbip, hbo, hbr, hbrc, hbc, hbfr⟩

end NearQuarticWires.StageMain.Controller
