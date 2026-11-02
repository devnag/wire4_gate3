import Proof.Quartic.StageMain.SampleConfigure
import Proof.Quartic.StageMain.SamplingReady
import Proof.Quartic.StageMain.SerializerBounds

/-!
# The complete sampled pass after finite-source acquisition

Step 4 of `sec:algorithm`, paper/paper.tex,
loads the sample dimensions, scans the chosen seed once, traverses the
actual certified-column bitmap, and writes the exact framed Step 5
record. The numeric capacities below concern only the concrete codecs,
counters, and ordinary-call reservations of these programs.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.Controller

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open StageLift Compact SampleCells

def activeTail : St VV MM := .seq configureSamples
  (.seq prepareSamplePass (.seq columnsPass serializeMain))

noncomputable def activeTailCost {B1 B2 : ℕ} (c : Call) (p : Program.Selected c)
    (w : List Bool) (parameterCursor T : ℕ) : ℕ :=
  parameterCursor + 291 + (19 * 2 ^ (c.n - p.1.k) + 188 * p.1.ellf + 329) +
    (2 ^ (c.n - p.1.k) * (p.1.Q * (T + 4) + 13) + 12) +
    (3 * (13 * (fieldPrintBound c (Program.mainWord B1 B2 c w).length + 1) + 3) + 2) + 3

theorem PrintSource.of_parameterRest {c : Call} {p : Cells.Parameters} {a b : DS VV MM}
    (h : PrintSource c p a) (hr : parameterRest b = parameterRest a)
    (hcursor : b.rc parameterStore ≤ 46) : PrintSource c p b := by
  rcases (by simpa only [parameterRest, Prod.mk.injEq] using hr) with
    ⟨_hi, _ho, hram, hrc, _hkin, _hkout, _hkc⟩
  refine ⟨hram ▸ h.call, hram ▸ h.parameters, ?_, hcursor⟩
  have he := congrFun hrc callStore
  simp only [Function.update_of_ne (by decide : callStore ≠ parameterStore)] at he
  rw [he]
  exact h.callCursor

theorem PrintSource.of_ram_rc {c : Call} {p : Cells.Parameters} {a b : DS VV MM}
    (h : PrintSource c p a) (hr : b.ram = a.ram) (hc : b.rc = a.rc) : PrintSource c p b :=
  ⟨hr ▸ h.call, hr ▸ h.parameters, hc ▸ h.callCursor, hc ▸ h.parameterCursor⟩

theorem activeTail_run {B1 B2 : ℕ} {budget : EntryRequest B1 B2 → ℕ}
    (f : WordFunction (EntryRequest B1 B2) entryWord entryOutput budget)
    {c : Call} {p : Program.Selected c} (hd : Program.dispatch B1 B2 c = some p)
    (w : List Bool) (width : ℕ) (input : List Bool) (L B T : ℕ)
    (h : SamplingBounds f hd w width L B T) (rest : List Bool)
    (a : DS VV MM) (hc : Cst a) (hs : PrintSource c p.1 a)
    (hout : a.out = []) (hkin : a.kin = [])
    (hbits : a.ram compactStore = (Program.prepWord B1 B2 c w).map Bool.toNat)
    (hlen : a.env compactLength = (Program.prepWord B1 B2 c w).length)
    (hcursor : a.rc compactStore = (Program.prepWord B1 B2 c w).length)
    (hin : input.drop a.ip = frame (Program.certifiedBits (Program.runCall c p w)) ++
      bitWord (Program.consistentBit (Program.runCall c p w)) ++ frame (Program.runCall c p w).chosenSeed ++
      binary p.1.ellf (Program.runCall c p w).seed.modulus ++ rest)
    (hindex : 46 < 2 ^ width) (hseed : 8 * p.1.ellf < width)
    (hN : 2 ^ (c.n - p.1.k) < 2 ^ width)
    (htotal : 2 ^ (c.n - p.1.k) * p.1.Q < 2 ^ width)
    (houtput : (Program.mainWord B1 B2 c w).length + 2 ≤ width) :
    Hs (taggedContext width input f L B) activeTail a
      (activeTailCost (B1 := B1) (B2 := B2) c p w (a.rc parameterStore) T)
      (fun b => b.out = frame (Program.mainWord B1 B2 c w)) := by
  let C := taggedContext width input f L B
  let readyTime := 19 * 2 ^ (c.n - p.1.k) + 188 * p.1.ellf + 329
  let passTime := 2 ^ (c.n - p.1.k) * (p.1.Q * (T + 4) + 13) + 12
  let printTime := 3 * (13 * (fieldPrintBound c (Program.mainWord B1 B2 c w).length + 1) + 3) + 2
  unfold activeTail
  refine (Hs.seq (t2 := readyTime + (passTime + printTime + 1) + 1)
    (configureSamples_run C p.1 a hc hs.parameters (by change 18 < 2 ^ width; omega)) ?_).mono
      (by unfold activeTailCost; dsimp only [readyTime, passTime, printTime]; omega) (fun _ h => h)
  rintro b ⟨hbE, hbQ, hbcursor, hbrest, hbc, hbfr⟩
  have hbs : PrintSource c p.1 b := hs.of_parameterRest hbrest (by rw [hbcursor]; decide)
  rcases (by simpa only [parameterRest, Prod.mk.injEq] using hbrest) with
    ⟨hbip, hbo, hbram, hbrc, hbkin, _hbkout, _hbkc⟩
  have hbcompact : b.rc compactStore = a.rc compactStore := by
    have he := congrFun hbrc compactStore
    simpa only [Function.update_of_ne (by decide : compactStore ≠ parameterStore)] using he
  refine Hs.seq (t1 := readyTime) (t2 := passTime + printTime + 1)
    (prepareSamplePass_run C c p w rest b hbc hbE hbQ (hbkin.trans hkin)
      (by rw [hbram]; exact hbits) ((hbfr compactLength (by decide)).trans hlen)
      (hbcompact.trans hcursor) (by rw [hbip]; exact hin) h.widthOk hN hseed
      ((show p.1.ellf < width by have hw := h.widthOk; omega).trans Nat.lt_two_pow_self)
      (by change 1 < 2 ^ width; omega)) ?_
  rintro d ⟨hdr, hdnc, hdN, hdcon, hdip, hdrest, hdc, _hdfr⟩
  rcases (by simpa only [Prod.mk.injEq] using hdrest) with
    ⟨hdo, hdram, hdrc, _hdkin, _hdkout, _hdkc⟩
  have hds : PrintSource c p.1 d := hbs.of_ram_rc hdram hdrc
  have hdout : d.out = [] := hdo.trans (hbo.trans hout)
  have hbitmap : input.drop a.ip = frame (Program.certifiedBits (Program.runCall c p w)) ++
      (bitWord (Program.consistentBit (Program.runCall c p w)) ++ frame (Program.runCall c p w).chosenSeed ++
        binary p.1.ellf (Program.runCall c p w).seed.modulus ++ rest) := by
    simpa only [List.append_assoc] using hin
  refine Hs.seq (t1 := passTime) (t2 := printTime)
    (columnsPass_run f hd w width input L B T h a.ip _ hbitmap d hdc hdr
      (hdip.trans hbip) hdN hN htotal) ?_
  rintro e ⟨heA, heM, _her, _heip, heo, heram, herc, hec, hefr⟩
  refine (serializeMain_actual C hd w e hec (hds.of_ram_rc heram herc) (heo.trans hdout)
    ((hefr certifiedCount (by decide)).trans hdnc)
    ((hefr consistency (by decide)).trans hdcon) heA heM hindex houtput).mono le_rfl ?_
  rintro z ⟨hzo, _⟩
  exact hzo

end NearQuarticWires.StageMain.Controller
