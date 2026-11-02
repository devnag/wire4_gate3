import Proof.Quartic.StageMain.DefaultCopy
import Proof.Quartic.StageMain.CompactBounds
import Proof.Quartic.StageOutput.DefaultRaw

/-!
# Passing a completed interval through the main stage

The default cases of `sec:params`, paper/paper.tex, have already computed the final interval. The main stage
copies its six encoded scalars and false tag, writes an exact frame,
and does not copy the appended primitive-field cache.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.Controller

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces

theorem copyRawCost_le (xs : List ℕ) (R : ℕ)
    (hb : ∀ v ∈ xs, natBitLength v ≤ R) :
    copyRawCost xs ≤ xs.length * (70 * R + 72) + 1 := by
  induction xs with
  | nil => simp [copyRawCost]
  | cons v xs ih =>
    have hv := hb v (by simp)
    have hi := ih (fun x hx => hb x (by simp [hx]))
    simp only [copyRawCost, List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul,
      Nat.one_mul] at hi ⊢
    omega

def defaultMainRaw : St VV MM := .seq (.op (.emit false)) (copyRawNaturals 6)

def defaultMain : St VV MM := framedOutputProgram defaultMainRaw

theorem defaultMain_run (C : Ctx) (q : ℚ × ℚ) (rest : List Bool)
    (a : DS VV MM) (hc : Cst a) (hout : a.out = [])
    (hin : C.inp.drop a.ip = outputWord q ++ rest)
    (hword : (outputWord q).length ≤ 24) (hwidth : 26 ≤ C.Wd) :
    Hs C defaultMain a 50000 (fun b => b.out = frame (false :: outputWord q)) := by
  let xs := StageOutput.rationalDigits q
  have hxs : xs.length = 6 := StageOutput.rationalDigits_length q
  have hwordeq : xs.flatMap natWord = outputWord q := StageOutput.rationalDigits_word q
  have hbits : ∀ v ∈ xs, natBitLength v ≤ 24 := by
    intro v hv
    have hh := (NearCubicGates.Close.Dispatch.natBitLength_le_len v).trans
      (Compact.natWord_length_mem v xs hv)
    rw [hwordeq] at hh
    exact hh.trans hword
  let d : DS VV MM := { a with out := a.out ++ [false] }
  have hemit : Ex C (.op (.emit false)) a d 1 := Ex.op (OpEx.emit false a)
  have hh := copyRawNaturals_run C xs rest
    (fun v hv => by have hb := hbits v hv; omega) d ⟨hc.z, hc.one, hc.two⟩
    (by rw [hwordeq]; exact hin)
  rw [hxs] at hh
  obtain ⟨b, n, he, hn, hbo, _hbi, _hbrest, _hbc⟩ := hh
  have hraw : Ex C defaultMainRaw a b (1 + n + 1) := Ex.seq hemit he
  have hbword : b.out = false :: outputWord q := by
    rw [hbo, hwordeq]
    simp only [d, hout, List.nil_append, List.singleton_append]
  have hmarked : markOutputState a = a := by
    unfold markOutputState
    simp only [hout, List.flatMap_nil]
    rw [← hout]
  have hf := framedOutput_run hraw
  rw [hmarked] at hf
  refine ⟨{ b with out := frame b.out }, 3 * (1 + n + 1) + 2, hf, ?_, congrArg frame hbword⟩
  have hb := copyRawCost_le xs 24 hbits
  rw [hxs] at hb
  omega

end NearQuarticWires.StageMain.Controller
