import Proof.Quartic.StageMain.ColumnLoop

/-!
# Exact totals from the complete certificate stream

Step 4 of `sec:algorithm`, paper/paper.tex,
initializes both totals, traverses every column, and consumes the final
certificate delimiter. The resulting integers are the literal sums
passed to Step 5; the finite source and seed remain available.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.Controller

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open Compact SampleCells

def columnPassScratch : List (Fin VV) := columnLimit :: columnScratch

theorem MainRetained.pass_frame {B1 B2 : ℕ} {c : Call} {p : Program.Selected c}
    {w : List Bool} {a b : DS VV MM} (h : MainRetained B1 B2 c p w a)
    (hkin : b.kin = []) (hram : b.ram = a.ram) (hrc : b.rc = a.rc)
    (hf : Fr a b columnPassScratch) : MainRetained B1 B2 c p w b := by
  refine ⟨⟨(hf ell (by decide)).trans h.coefficients.degree,
    (hf modulus (by decide)).trans h.coefficients.field, ?_⟩,
    hkin, (congrFun hram compactStore).trans h.bits,
    (hf compactLength (by decide)).trans h.length,
    (congrFun hrc compactStore).trans h.cursor,
    (hf sampleLimit (by decide)).trans h.samples⟩
  intro i
  have hi : coefficient i ∉ columnPassScratch := by fin_cases i <;> decide
  exact (hf _ hi).trans (h.coefficients.coeff i)

def initializeTotals : St VV MM := .seq (.op (.copy columnLimit columnCounter))
  (.seq (.op (.zero acceptanceTotal)) (.op (.zero maskTotal)))

def columnsPass : St VV MM :=
  .seq initializeTotals (.seq columnsLoop (.op (.rdI t0)))

theorem columnsPass_run {B1 B2 : ℕ} {budget : EntryRequest B1 B2 → ℕ}
    (f : WordFunction (EntryRequest B1 B2) entryWord entryOutput budget)
    {c : Call} {p : Program.Selected c} (hd : Program.dispatch B1 B2 c = some p)
    (w : List Bool) (width : ℕ) (input : List Bool) (L B T : ℕ)
    (h : SamplingBounds f hd w width L B T) (base : ℕ) (rest : List Bool)
    (hin : input.drop base = frame (Program.certifiedBits (Program.runCall c p w)) ++ rest)
    (a : DS VV MM) (hc : Cst a) (hr : MainRetained B1 B2 c p w a)
    (hip : a.ip = base) (hN : a.env columnCounter = 2 ^ (c.n - p.1.k))
    (hNfit : 2 ^ (c.n - p.1.k) < 2 ^ width)
    (hfit : 2 ^ (c.n - p.1.k) * p.1.Q < 2 ^ width) :
    Hs (taggedContext width input f L B) columnsPass a
      (2 ^ (c.n - p.1.k) * (p.1.Q * (T + 4) + 13) + 12) (fun b =>
      (b.env acceptanceTotal : ℤ) = Program.acceptTotal (Program.runCall c p w) ∧
      (b.env maskTotal : ℤ) = Program.maskTotal (Program.runCall c p w) ∧
      MainRetained B1 B2 c p w b ∧
      b.ip = base + 2 * 2 ^ (c.n - p.1.k) + 1 ∧
      b.out = a.out ∧ b.ram = a.ram ∧ b.rc = a.rc ∧ Cst b ∧
      Fr a b columnPassScratch) := by
  let C := taggedContext width input f L B
  let s := ((a.set columnLimit (a.env columnCounter)).set acceptanceTotal 0).set maskTotal 0
  have hs : Ex C initializeTotals a s 5 :=
    Ex.seq (Ex.op (OpEx.copy columnLimit columnCounter a (by decide)))
      (Ex.seq (Ex.op (OpEx.zero acceptanceTotal _)) (Ex.op (OpEx.zero maskTotal _)))
  have hsf : Fr a s columnPassScratch :=
    (Fr.set a _ (by decide)).trans
      ((Fr.set _ _ (by decide)).trans (Fr.set _ _ (by decide)))
  have hsc : Cst s := Cst.of_fr hc hsf (by decide)
  have hsr : MainRetained B1 B2 c p w s := hr.pass_frame hr.kin rfl rfl hsf
  have hsA : s.env acceptanceTotal = 0 := by dsimp only [s]; rw [DS.set_env_ne _ _ (by decide), DS.set_env_self]
  have hsM : s.env maskTotal = 0 := DS.set_env_self _ _ _
  have hsN : s.env columnLimit = 2 ^ (c.n - p.1.k) := by
    dsimp only [s]
    rw [DS.set_env_ne _ _ (by decide), DS.set_env_ne _ _ (by decide), DS.set_env_self, hN]
  have he := columnsLoop_run f hd w width input L B T h base rest hin s hsc hsr hip hsN hNfit
    (by rw [hsA, Nat.zero_add]; exact hfit) (by rw [hsM, Nat.zero_add]; exact hfit)
  obtain ⟨b, n, hbex, hbn, hbA, hbM, _hbi, _hbl, hbr, hbip, hbo, hbram, hbrc, hbc, hbf⟩ := he
  have hread : b.ip < input.length := by
    rw [hbip]
    apply lt_of_drop hin (2 * 2 ^ (c.n - p.1.k))
    rw [frame_length]
    simp only [Program.certifiedBits, List.length_ofFn]
    change 2 * 2 ^ (c.n - p.1.k) < 2 * 2 ^ (c.n - p.1.k) + 1
    omega
  let d : DS VV MM := { b.set t0 (bitOf input b.ip) with ip := b.ip + 1 }
  have hdf : Fr b d columnPassScratch := Fr.set b _ (by decide)
  refine ⟨d, 5 + (n + 1 + 1) + 1, Ex.seq hs (Ex.seq hbex (Ex.op (OpEx.rdI t0 b hread))),
    by omega, ?_⟩
  refine ⟨?_, ?_, hbr.pass_frame hbr.kin rfl rfl hdf, by dsimp only [d]; rw [hbip],
    hbo, hbram, hbrc, Cst.of_fr hbc hdf (by decide),
    hsf.trans ((hbf.weaken (fun _ hx => List.mem_cons_of_mem _ hx)).trans hdf)⟩
  · have hval : d.env acceptanceTotal = columnAcceptancePrefix (Program.runCall c p w)
        (2 ^ (c.n - p.1.k)) := by
      change (b.set t0 (bitOf input b.ip)).env acceptanceTotal = _
      rw [DS.set_env_ne _ _ (by decide), hbA, hsA, Nat.zero_add]
    rw [hval]
    exact columnAcceptancePrefix_cast (Program.runCall c p w)
  · have hval : d.env maskTotal = columnMaskPrefix (Program.runCall c p w)
        (2 ^ (c.n - p.1.k)) := by
      change (b.set t0 (bitOf input b.ip)).env maskTotal = _
      rw [DS.set_env_ne _ _ (by decide), hbM, hsM, Nat.zero_add]
    rw [hval]
    exact columnMaskPrefix_cast (Program.runCall c p w)

end NearQuarticWires.StageMain.Controller
