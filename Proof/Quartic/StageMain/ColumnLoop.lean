import Proof.Quartic.StageMain.ColumnBody

/-!
# The main pass over every certified-column bit

Step 4 of `sec:algorithm`, paper/paper.tex,
traverses the actual bitmap once. Its counted loop skips uncertified
columns and accumulates the exact two integer sums without storing
samples or a second certificate bitmap.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.Controller

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open SampleCells

def columnsLoop : St VV MM := forS columnCounter columnLimit columnBody

theorem columnsLoop_run {B1 B2 : ℕ} {budget : EntryRequest B1 B2 → ℕ}
    (f : WordFunction (EntryRequest B1 B2) entryWord entryOutput budget)
    {c : Call} {p : Program.Selected c} (hd : Program.dispatch B1 B2 c = some p)
    (w : List Bool) (width : ℕ) (input : List Bool) (L B T : ℕ)
    (h : SamplingBounds f hd w width L B T) (base : ℕ) (rest : List Bool)
    (hin : input.drop base = frame (Program.certifiedBits (Program.runCall c p w)) ++ rest)
    (a : DS VV MM) (hc : Cst a) (hr : MainRetained B1 B2 c p w a)
    (hip : a.ip = base) (hN : a.env columnLimit = 2 ^ (c.n - p.1.k))
    (hNfit : 2 ^ (c.n - p.1.k) < 2 ^ width)
    (hA : a.env acceptanceTotal + 2 ^ (c.n - p.1.k) * p.1.Q < 2 ^ width)
    (hM : a.env maskTotal + 2 ^ (c.n - p.1.k) * p.1.Q < 2 ^ width) :
    Hs (taggedContext width input f L B) columnsLoop a
      (2 ^ (c.n - p.1.k) * (p.1.Q * (T + 4) + 13) + 4) (fun b =>
      b.env acceptanceTotal = a.env acceptanceTotal +
        columnAcceptancePrefix (Program.runCall c p w) (2 ^ (c.n - p.1.k)) ∧
      b.env maskTotal = a.env maskTotal +
        columnMaskPrefix (Program.runCall c p w) (2 ^ (c.n - p.1.k)) ∧
      b.env columnCounter = 2 ^ (c.n - p.1.k) ∧ b.env columnLimit = 2 ^ (c.n - p.1.k) ∧
      MainRetained B1 B2 c p w b ∧ b.ip = base + 2 * 2 ^ (c.n - p.1.k) ∧
      b.out = a.out ∧ b.ram = a.ram ∧ b.rc = a.rc ∧ Cst b ∧ Fr a b columnScratch) := by
  let C := taggedContext width input f L B
  let cc := Program.runCall c p w
  have hQ : cc.seed.Q = p.1.Q := rfl
  let N := 2 ^ (c.n - p.1.k)
  let I : ℕ → DS VV MM → Prop := fun k b =>
    MainRetained B1 B2 c p w b ∧
    b.env acceptanceTotal = a.env acceptanceTotal + columnAcceptancePrefix cc k ∧
    b.env maskTotal = a.env maskTotal + columnMaskPrefix cc k ∧
    b.ip = base + 2 * k ∧ b.out = a.out ∧ b.ram = a.ram ∧ b.rc = a.rc ∧
    Cst b ∧ Fr a b columnScratch
  have hI : ∀ k b value, I k b → I k (b.set columnCounter value) := by
    rintro k b value ⟨hbr, hbA, hbM, hbi, hbo, hbram, hbrc, hbc, hbf⟩
    have hf : Fr b (b.set columnCounter value) columnScratch :=
      Fr.set b _ (by simp [columnScratch])
    exact ⟨hbr.frame hbr.kin rfl rfl hf,
      by rw [DS.set_env_ne _ _ (by decide)]; exact hbA,
      by rw [DS.set_env_ne _ _ (by decide)]; exact hbM,
      hbi, hbo, hbram, hbrc, Cst.of_fr hbc hf (by decide), hbf.trans hf⟩
  have h0 : I 0 a := ⟨hr, by simp [columnAcceptancePrefix], by simp [columnMaskPrefix],
    by simpa using hip, rfl, rfl, rfl, hc, Fr.refl _ _⟩
  unfold columnsLoop
  refine (forS_spec' (C := C) columnCounter columnLimit (by decide) columnBody a N hNfit I
    (p.1.Q * (T + 4) + 9) hI h0 hN ?_).mono (by dsimp only [N]; exact le_of_eq (by ring)) ?_
  · rintro k hk b ⟨hbr, hbA, hbM, hbi, hbo, hbram, hbrc, hbc, hbf⟩ hbindex hblimit
    let z : Fin N := ⟨k, hk⟩
    have hkq : k * p.1.Q + p.1.Q ≤ N * p.1.Q := by
      calc
        _ = (k + 1) * p.1.Q := by ring
        _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
    have hpA := columnAcceptancePrefix_le cc k
    have hpM := columnMaskPrefix_le cc k
    rw [hQ] at hpA hpM
    refine (columnBody_run f hd w z width input L B T h base rest hin b hbc hbr hbindex hbi
      (by rw [hbA]; change a.env acceptanceTotal + N * p.1.Q < 2 ^ width at hA; omega)
      (by rw [hbM]; change a.env maskTotal + N * p.1.Q < 2 ^ width at hM; omega)).mono le_rfl ?_
    rintro d ⟨hdA, hdM, hdr, hdi, hdo, hdram, hdrc, hdc, hdfr⟩
    have hdf : Fr b d columnScratch := hdfr.weaken (fun _ hx => List.mem_cons_of_mem _ hx)
    refine ⟨⟨hdr, ?_, ?_, hdi, hdo.trans hbo, hdram.trans hbram,
      hdrc.trans hbrc, hdc, hbf.trans hdf⟩,
      (hdfr columnCounter (by decide)).trans hbindex,
      (hdfr columnLimit (by decide)).trans hblimit⟩
    · rw [hdA, hbA]
      have he := columnAcceptancePrefix_succ cc z
      change columnAcceptancePrefix cc (k + 1) = _ at he
      rw [he]
      exact Nat.add_assoc _ _ _
    · rw [hdM, hbM]
      have he := columnMaskPrefix_succ cc z
      change columnMaskPrefix cc (k + 1) = _ at he
      rw [he]
      exact Nat.add_assoc _ _ _
  · rintro b ⟨⟨hbr, hbA, hbM, hbi, hbo, hbram, hbrc, hbc, hbf⟩, hbindex, hblimit⟩
    exact ⟨hbA, hbM, hbindex, hblimit, hbr, hbi, hbo, hbram, hbrc, hbc, hbf⟩

end NearQuarticWires.StageMain.Controller
