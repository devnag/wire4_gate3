import Proof.Quartic.StageMain.ColumnState
import Proof.Quartic.StageMain.ColumnSums

/-!
# The certified-column branch of the main pass

Step 4 of `sec:algorithm`, paper/paper.tex,
reads each actual certificate bit and runs all sample labels exactly
when that bit is true. Uncertified columns leave both totals unchanged.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.Controller

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open Compact SampleCells

variable {B1 B2 : ℕ} {budget : EntryRequest B1 B2 → ℕ}

def sampleIfCertified : St VV MM := .ite (.eq certifiedFlag v1) sampleLoop skipS

theorem sampleIfCertified_run
    (f : WordFunction (EntryRequest B1 B2) entryWord entryOutput budget)
    {c : Call} {p : Program.Selected c} (hd : Program.dispatch B1 B2 c = some p)
    (w : List Bool) (z : Fin (2 ^ (c.n - p.1.k)))
    (width : ℕ) (input : List Bool) (L B T : ℕ) (h : SamplingBounds f hd w width L B T)
    (a : DS VV MM) (hc : Cst a) (hr : MainRetained B1 B2 c p w a)
    (hcol : a.env columnCounter = z.val)
    (hflag : a.env certifiedFlag = (decide (z ∈ (Program.runCall c p w).certifiedColumns)).toNat)
    (hA : a.env acceptanceTotal + p.1.Q < 2 ^ width)
    (hM : a.env maskTotal + p.1.Q < 2 ^ width) :
    Hs (taggedContext width input f L B) sampleIfCertified a (p.1.Q * (T + 4) + 5) (fun b =>
      b.env acceptanceTotal = a.env acceptanceTotal + certifiedAcceptance (Program.runCall c p w) z ∧
      b.env maskTotal = a.env maskTotal + certifiedMask (Program.runCall c p w) z ∧
      MainRetained B1 B2 c p w b ∧ b.ip = a.ip ∧ b.out = a.out ∧ b.ram = a.ram ∧
      b.rc = a.rc ∧ Cst b ∧ Fr a b columnBodyScratch) := by
  classical
  refine Hs.ite (c := .eq certifiedFlag v1) (t := p.1.Q * (T + 4) + 4)
    (show certifiedFlag ≠ v1 by decide) ?_ ?_
  · intro he
    have hz : z ∈ (Program.runCall c p w).certifiedColumns := by
      by_contra hn
      simp [Cnd.eval, hflag, hc.one, hn] at he
    have hca : certifiedAcceptance (Program.runCall c p w) z =
        sampleAcceptancePrefix (Program.runCall c p w) z p.1.Q := if_pos hz
    have hcm : certifiedMask (Program.runCall c p w) z =
        sampleMaskPrefix (Program.runCall c p w) z p.1.Q := if_pos hz
    refine (sampleLoop_retained f hd w z width input L B T h a hc hr hcol hA hM).mono le_rfl ?_
    rintro b ⟨hbA, hbM, hbr, hbi, hbo, hbram, hbrc, hbc, hbfr⟩
    exact ⟨by rw [hca]; exact hbA, by rw [hcm]; exact hbM, hbr, hbi, hbo, hbram, hbrc, hbc,
      hbfr.weaken (fun _ hx => List.mem_append_right _ hx)⟩
  · intro he
    have hz : z ∉ (Program.runCall c p w).certifiedColumns := by
      intro hm
      simp [Cnd.eval, hflag, hc.one, hm] at he
    have hca : certifiedAcceptance (Program.runCall c p w) z = 0 := if_neg hz
    have hcm : certifiedMask (Program.runCall c p w) z = 0 := if_neg hz
    refine (skip_spec a).mono (by omega) ?_
    rintro b rfl
    have hf : Fr a (a.set vJ 0) columnBodyScratch := Fr.set a _ (by decide)
    exact ⟨by simp only [hca, Nat.add_zero, DS.set_env_ne _ _ (by decide : acceptanceTotal ≠ vJ)],
      by simp only [hcm, Nat.add_zero, DS.set_env_ne _ _ (by decide : maskTotal ≠ vJ)],
      hr.frame hr.kin rfl rfl (hf.weaken (fun _ hx => List.mem_cons_of_mem _ hx)), rfl, rfl, rfl, rfl, Cst.of_fr hc hf (by decide), hf⟩

def columnBody : St VV MM := .seq readColumnFlag sampleIfCertified

theorem columnBody_run
    (f : WordFunction (EntryRequest B1 B2) entryWord entryOutput budget)
    {c : Call} {p : Program.Selected c} (hd : Program.dispatch B1 B2 c = some p)
    (w : List Bool) (z : Fin (2 ^ (c.n - p.1.k)))
    (width : ℕ) (input : List Bool) (L B T : ℕ) (h : SamplingBounds f hd w width L B T)
    (base : ℕ) (rest : List Bool)
    (hin : input.drop base = frame (Program.certifiedBits (Program.runCall c p w)) ++ rest)
    (a : DS VV MM) (hc : Cst a) (hr : MainRetained B1 B2 c p w a)
    (hcol : a.env columnCounter = z.val) (hip : a.ip = base + 2 * z.val)
    (hA : a.env acceptanceTotal + p.1.Q < 2 ^ width)
    (hM : a.env maskTotal + p.1.Q < 2 ^ width) :
    Hs (taggedContext width input f L B) columnBody a (p.1.Q * (T + 4) + 9) (fun b =>
      b.env acceptanceTotal = a.env acceptanceTotal + certifiedAcceptance (Program.runCall c p w) z ∧
      b.env maskTotal = a.env maskTotal + certifiedMask (Program.runCall c p w) z ∧
      MainRetained B1 B2 c p w b ∧ b.ip = base + 2 * (z.val + 1) ∧
      b.out = a.out ∧ b.ram = a.ram ∧ b.rc = a.rc ∧ Cst b ∧ Fr a b columnBodyScratch) := by
  let C := taggedContext width input f L B
  unfold columnBody
  refine (Hs.seq (t1 := 3) (t2 := p.1.Q * (T + 4) + 5)
    (readCertifiedFlag_run C (Program.runCall c p w) rest base z a hc hin hip) ?_).mono
      (by omega) (fun _ h => h)
  rintro b ⟨hbflag, hbip, hbrest, hbc, hbfr⟩
  have hbf : Fr a b columnBodyScratch := hbfr.weaken (fun _ hx => List.mem_append_left _ hx)
  rcases (by simpa only [Prod.mk.injEq] using hbrest) with ⟨hbo, hbr, hbrc, hbkin, _hbkout, _hbkc⟩
  have hret : MainRetained B1 B2 c p w b := hr.frame (hbkin.trans hr.kin) hbr hbrc
    (hbf.weaken (fun _ hx => List.mem_cons_of_mem _ hx))
  refine (sampleIfCertified_run f hd w z width input L B T h b hbc hret
    ((hbfr columnCounter (by decide)).trans hcol) hbflag
    (by rw [hbfr acceptanceTotal (by decide)]; exact hA)
    (by rw [hbfr maskTotal (by decide)]; exact hM)).mono le_rfl ?_
  rintro d ⟨hdA, hdM, hdr, hdip, hdo, hdram, hdrc, hdc, hdfr⟩
  exact ⟨by rw [hdA, hbfr acceptanceTotal (by decide)],
    by rw [hdM, hbfr maskTotal (by decide)], hdr, hdip.trans hbip,
    hdo.trans hbo, hdram.trans hbr, hdrc.trans hbrc, hdc, hbf.trans hdfr⟩

end NearQuarticWires.StageMain.Controller
