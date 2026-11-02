import Proof.Quartic.StageMain.ActiveTail
import Proof.Quartic.StageMain.FieldCache
import Proof.Gates.Cells.Inv

/-!
# Acquisition and execution of the main pass from its actual source

Step 4 of `sec:algorithm`, paper/paper.tex,
reads the original finite preparation prefix, retains it, and computes
the sampled totals from the actual certificate and chosen seed. The
only appended data is the primitive field cache computed once by
`imp:seed`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.Controller

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open StageLift Compact SampleCells

theorem cachedMainWord_compact {B1 B2 : ℕ} {c : Call} {p : Program.Selected c}
    (hd : Program.dispatch B1 B2 c = some p) (w : List Bool) :
    cachedMainWord B1 B2 c w = compactInput c p.1 (Program.witnessPrefix c p.1 w) ++
      (frame (Program.certifiedBits (Program.runCall c p w)) ++
       bitWord (Program.consistentBit (Program.runCall c p w)) ++
       frame (Program.runCall c p w).chosenSeed ++
       binary p.1.ellf (Program.runCall c p w).seed.modulus) := by
  have hf : mainFieldBits B1 B2 c = binary p.1.ellf (Program.runCall c p w).seed.modulus := by
    simp only [mainFieldBits, mainFieldDegree, hd]
    rfl
  rw [cachedMainWord, greedyWord_compact_layout hd, hf]
  simp only [List.append_assoc]

def activeAcquire : St VV MM := .seq initializeCompact activeTail

noncomputable def activeAcquireCost {B1 B2 : ℕ} (c : Call) (p : Program.Selected c)
    (w : List Bool) (T : ℕ) : ℕ :=
  initializeCost c p.1 (Program.witnessPrefix c p.1 w)
      (compactInput c p.1 (Program.witnessPrefix c p.1 w)).length +
    activeTailCost (B1 := B1) (B2 := B2) c p w 46 T + 1

theorem activeAcquire_run {B1 B2 : ℕ} {budget : EntryRequest B1 B2 → ℕ}
    (f : WordFunction (EntryRequest B1 B2) entryWord entryOutput budget)
    {c : Call} {p : Program.Selected c} (hd : Program.dispatch B1 B2 c = some p)
    (w : List Bool) (width : ℕ) (input : List Bool) (L B T : ℕ)
    (hinput : input = cachedMainWord B1 B2 c w)
    (h : SamplingBounds f hd w width L B T)
    (a : DS VV MM) (hc : Cst a) (hip : a.ip = 0) (hout : a.out = []) (hkin : a.kin = [])
    (hempty : ∀ store, a.ram store = [] ∧ a.rc store = 0)
    (hcompact : (compactInput c p.1 (Program.witnessPrefix c p.1 w)).length + 2 ≤ width)
    (hindex : 46 < 2 ^ width) (hseed : 8 * p.1.ellf < width)
    (hN : 2 ^ (c.n - p.1.k) < 2 ^ width)
    (htotal : 2 ^ (c.n - p.1.k) * p.1.Q < 2 ^ width)
    (houtput : (Program.mainWord B1 B2 c w).length + 2 ≤ width) :
    Hs (taggedContext width input f L B) activeAcquire a
      (activeAcquireCost (B1 := B1) (B2 := B2) c p w T)
      (fun b => b.out = frame (Program.mainWord B1 B2 c w)) := by
  let C := taggedContext width input f L B
  let witness := Program.witnessPrefix c p.1 w
  let tail := frame (Program.certifiedBits (Program.runCall c p w)) ++
    bitWord (Program.consistentBit (Program.runCall c p w)) ++
    frame (Program.runCall c p w).chosenSeed ++
    binary p.1.ellf (Program.runCall c p w).seed.modulus
  have hin : C.inp.drop a.ip = compactInput c p.1 witness ++ tail := by
    change input.drop a.ip = _
    rw [hip, List.drop_zero, hinput, cachedMainWord_compact hd]
  obtain ⟨hprefix, hcap, hfields, hprime, hfactor⟩ :=
    compact_decoder_bounds c p.1 witness width hcompact
  obtain ⟨b, n, he, hn, hbip, hbdata, hblen, hbbits, hbcursor, hbrest, hbc, _hbfr⟩ :=
    initialize_run C c p.1 (compactInput c p.1 witness).length witness tail a hc hin
      hprefix hcap hfields hcompact ⟨hprime, hfactor⟩ (fun store _ => hempty store)
  have hbcur := he.rc_le (by intro store; rw [(hempty store).1, (hempty store).2]; rfl)
  have hbs : PrintSource c p.1 b := ⟨hbdata.originalCall, hbdata.scalarFields,
    by have hh := hbcur callStore; simpa [hbdata.originalCall] using hh,
    by have hh := hbcur parameterStore; simpa [hbdata.scalarFields, parameterScalars_length] using hh⟩
  have hbin : input.drop b.ip = tail := by
    rw [hbip]
    exact drop_adv hin
  have ho : b.out = [] := (congrArg (fun t => t.1) hbrest).trans hout
  have hk : b.kin = [] := (congrArg (fun t => t.2.1) hbrest).trans hkin
  have hlen : b.env compactLength = (Program.prepWord B1 B2 c w).length := by
    rw [prepWord_eq_compact hd]
    exact hblen
  have hbits : b.ram compactStore = (Program.prepWord B1 B2 c w).map Bool.toNat := by
    rw [prepWord_eq_compact hd]
    exact hbbits
  have hcursor : b.rc compactStore = (Program.prepWord B1 B2 c w).length := by
    rw [prepWord_eq_compact hd]
    exact hbcursor
  have ht := activeTail_run f hd w width input L B T h [] b hbc hbs ho hk hbits hlen hcursor
    (by simpa only [List.append_nil] using hbin) hindex hseed hN htotal houtput
  obtain ⟨d, k, hde, hkn, hdo⟩ := ht
  exact ⟨d, n + k + 1, Ex.seq he hde,
    by have hh := hbs.parameterCursor; dsimp only [witness] at hn
       unfold activeAcquireCost activeTailCost at *; omega,
    hdo⟩

end NearQuarticWires.StageMain.Controller
