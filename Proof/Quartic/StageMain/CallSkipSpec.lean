import Proof.Quartic.StageMain.CallSkipList

/-!
# Composition of measured call scanners

`prop:time`, paper/paper.tex: sequential records and
counted lists are scanned with explicit bit-width and clock bounds.
The measured length is a runtime register value, not merely a
mathematical difference of input positions.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.CallSkip

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces

variable {α β : Type}

def ScanSpec (P : St VV MM) (encode : α → List Bool) (T : List (Fin VV))
    (cost : ℕ → ℕ) : Prop :=
  ∀ (C : Ctx) (L : ℕ) (a : DS VV MM), Cst a → ∀ (x : α) (rest : List Bool),
    C.inp.drop a.ip = encode x ++ rest → (encode x).length ≤ L → L + 2 ≤ C.Wd →
    a.env lengthCounter + (encode x).length < 2 ^ C.Wd →
    Hs C P a (cost L) (fun b => Scanned a b (encode x).length T)

theorem scanNat_spec : ScanSpec scanNat natWord atomScratch (fun L => 66 * (L + 1)) := by
  intro C L a hc x rest hin hlen hW hcap
  have hx : natBitLength x ≤ L := by rw [natWord_length] at hlen; omega
  exact (skipNat_run C a hc x rest hin (by omega) hcap).mono (by dsimp; omega) (fun _ h => h)

theorem ScanSpec.map {P : St VV MM} {encode : α → List Bool} {T : List (Fin VV)}
    {cost : ℕ → ℕ} (h : ScanSpec P encode T cost) (f : β → α) :
    ScanSpec P (fun x => encode (f x)) T cost := by
  intro C L a hc x rest hin hlen hW hcap
  exact h C L a hc (f x) rest hin hlen hW hcap

theorem ScanSpec.weaken {P : St VV MM} {encode : α → List Bool} {T U : List (Fin VV)}
    {cost bound : ℕ → ℕ} (h : ScanSpec P encode T cost)
    (hT : ∀ x ∈ T, x ∈ U) (hcost : ∀ L, cost L ≤ bound L) : ScanSpec P encode U bound := by
  intro C L a hc x rest hin hlen hW hcap
  refine (h C L a hc x rest hin hlen hW hcap).mono (hcost L) ?_
  intro b hb
  exact ⟨hb.pos, hb.unchanged, hb.constants, hb.registers.weaken hT, hb.bytes⟩

theorem ScanSpec.seq {P Q : St VV MM} {first second : α → List Bool}
    {T U : List (Fin VV)} {c d : ℕ → ℕ}
    (hP : ScanSpec P first T c) (hQ : ScanSpec Q second U d) :
    ScanSpec (.seq P Q) (fun x => first x ++ second x) (T ++ U)
      (fun L => c L + d L + 1) := by
  intro C L a hc x rest hin hlen hW hcap
  have hfirst : C.inp.drop a.ip = first x ++ (second x ++ rest) := by
    simpa only [List.append_assoc] using hin
  refine skipSeq_run C P Q a (first x) (second x) T U (c L) (d L)
    (hP C L a hc x _ hfirst (by simp only [List.length_append] at hlen; omega) hW
      (by simp only [List.length_append] at hcap; omega)) ?_
  intro b hb
  exact hQ C L b hb.constants x rest (hb.tail hfirst)
    (by simp only [List.length_append] at hlen; omega) hW
    (by rw [hb.bytes]; simp only [List.length_append] at hcap; omega)

theorem flatMap_item_length (encode : α → List Bool) (xs : List α) (x : α) (hx : x ∈ xs) :
    (encode x).length ≤ (xs.flatMap encode).length := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.mem_cons] at hx
    simp only [List.flatMap_cons, List.length_append]
    rcases hx with rfl | hx
    · omega
    · have := ih hx; omega

theorem list_count_le_length (encode : α → List Bool) (xs : List α)
    (hpos : ∀ x, 0 < (encode x).length) : xs.length ≤ (xs.flatMap encode).length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have := hpos x
    simp only [List.length_cons, List.flatMap_cons, List.length_append]
    omega

def listCost (cost : ℕ → ℕ) (L : ℕ) : ℕ := 30 * L + L * (cost L + 4) + 43

theorem ScanSpec.list {P : St VV MM} {encode : α → List Bool} {T : List (Fin VV)}
    {cost : ℕ → ℕ} (h : ScanSpec P encode T cost) (hpos : ∀ x, 0 < (encode x).length)
    (index count : Fin VV) (hne : index ≠ count)
    (hiSafe : index ∉ [vZ, v1, v2]) (hcSafe : count ∉ [vZ, v1, v2])
    (hiCounter : index ≠ lengthCounter) (hcCounter : count ≠ lengthCounter)
    (hcRead : count ≠ t3) (hiT : index ∉ T) (hcT : count ∉ T) :
    ScanSpec (skipList index count P) (listWord encode) (listScratch index count T)
      (listCost cost) := by
  intro C L a hc xs rest hin hlen hW hcap
  have hflat : (xs.flatMap encode).length ≤ L := by
    simp only [listWord, List.length_append] at hlen
    omega
  have hcount : xs.length ≤ L := (list_count_le_length encode xs hpos).trans hflat
  have hbits : natBitLength xs.length ≤ L := by
    simp only [listWord, List.length_append, natWord_length] at hlen
    omega
  have hfit : xs.length < 2 ^ C.Wd := lt_trans (by omega) Nat.lt_two_pow_self
  refine (skipList_run C index count hne hiSafe hcSafe hiCounter hcCounter hcRead P encode xs T
    hiT hcT (cost L) rest a hc hin (by omega) hfit hcap ?_).mono ?_ (fun _ h => h)
  · intro x hx b hbc tail hinput hbcost
    exact h C L b hbc x tail hinput ((flatMap_item_length encode xs x hx).trans hflat) hW hbcost
  · have hh := Nat.mul_le_mul_right (cost L + 4) hcount
    unfold listCost
    omega

end NearQuarticWires.StageMain.CallSkip
