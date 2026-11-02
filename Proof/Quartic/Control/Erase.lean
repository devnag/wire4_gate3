import Proof.Gates.Worker.Dock
import Proof.Amplification.RecoveryScratchErase

/-!
# Erasing the tapes of a subroutine in parallel

Paper: `prop:time`, paper/paper.tex: each step of the algorithm calls its subroutines (the child
evaluations of Step 3, one coefficient, one printed table, one exact system) many times, and is charged the running
time of each call plus a polynomial overhead.

A program that calls a word function repeatedly must return the tapes of the subroutine to blank between two calls.
The subroutine has an arbitrary number `t` of tapes; erasing them one after another costs a factor `t`. Here all of
them are erased in one sweep: the machine `RecoveryScratchErase.machine t` (imported from
`Proof.Amplification.RecoveryScratchErase`) moves all heads to the right together, writing `0` on every subroutine
tape, for as long as a driver tape reads `1`. Docked by `WMX.machZ`, which resets all heads in parallel, the erase of
`g` cells costs `2g + 4` steps, whatever `t` is.

* `eraseStep`: the sweep of `g` cells as a run of the machine;
* `eraseP`, `eraseP_exec`: the erase as a word program, on the streams of a bank, driven by a stream of `g` ones;
* `blank_overlay`: a stream that reads `0` from position `g` on reads `0` everywhere after the erase.
-/

set_option autoImplicit false

namespace NearQuarticWires.Control

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.ExtDecompositionBatch (Step)
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay)

variable {ns nr : ℕ}

/-- **The sweep as a run.** From all heads at `0`, the erase machine on `t` tapes and a driver of `g` ones runs
`g + 1` steps; every subroutine tape is overwritten with `0` on its first `g` cells, the driver is unchanged, and
all heads end at `g`. -/
theorem eraseStep (t g : ℕ) (backing : Fin t → List Bool) :
    Step (RecoveryScratchErase.machine t) (g + 1) (fun _ => 0)
      (Fin.addCases (motive := fun _ => List Bool) backing (fun _ : Fin 1 => List.replicate g true))
      (fun _ => g)
      (Fin.addCases (motive := fun _ => List Bool) (fun i => overlay (List.replicate g false) (backing i))
        (fun _ : Fin 1 => List.replicate g true)) := by
  have h := RecoveryScratchErase.sweep_prefix g 0 backing
  rw [Nat.zero_add] at h
  obtain ⟨r, hr, hf, _⟩ := h.run (by rfl)
  have hstart : RecoveryScratchErase.config 0 g 0 backing =
      (⟨(RecoveryScratchErase.machine t).start, fun _ => 0,
        Fin.addCases (motive := fun _ => List Bool) backing (fun _ : Fin 1 => List.replicate g true)⟩ :
        Configuration (t + 1) 2) := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp [RecoveryScratchErase.config, RecoveryScratchErase.tapes, overlay]
      · simp [RecoveryScratchErase.config, RecoveryScratchErase.tapes]
  rw [hstart] at hr
  refine Step.of_run hr ?_ ?_
  · rw [hf]; rfl
  · rw [hf]; rfl

/-- **The erase program**: the parallel sweep of the streams `bank j`, driven by the ones on `G`, with the heads
reset on the ruler `L`. -/
noncomputable def eraseP {t : ℕ} (bank : Fin t → Fin (ns + 1)) (G L : Fin (ns + 1)) : WMX ns nr :=
  WMX.machZ (RecoveryScratchErase.machine t) (Fin.addCases (motive := fun _ => Fin (ns + 1)) bank
    (fun _ : Fin 1 => G)) L

theorem bankG_injective {t : ℕ} (bank : Fin t → Fin (ns + 1)) (hinj : Function.Injective bank) (G : Fin (ns + 1))
    (hG : ∀ j, bank j ≠ G) :
    Function.Injective (Fin.addCases (motive := fun _ => Fin (ns + 1)) bank (fun _ : Fin 1 => G)) :=
  addCases_inj bank hinj G hG

/-- **The erase.** From heads `0` on the bank and on `G = 1^g`, with a blank ruler of at least `g + 1` cells, the
erase leaves `overlay 0^g` on every bank stream, `G` unchanged, all heads at `0`, and every other stream, every
register and the cell untouched, in `2g + 4` steps. -/
theorem eraseP_exec (cap : ℕ) {t : ℕ} (bank : Fin t → Fin (ns + 1)) (hinj : Function.Injective bank)
    (G L : Fin (ns + 1)) (hG : ∀ j, bank j ≠ G) (hL : ∀ j, bank j ≠ L) (hGL : G ≠ L) (g lcap : ℕ)
    (σ : WState ns nr) (h0 : ∀ j, σ.sh (bank j) = 0) (hGst : σ.st G = List.replicate g true) (hGsh : σ.sh G = 0)
    (hLst : σ.st L = List.replicate lcap false) (hLsh : σ.sh L = 0) (hcap : g + 1 ≤ lcap) :
    ∃ τ, WXExec cap (eraseP bank G L) σ τ (2 * (g + 1) + 2) ∧
      (∀ j, τ.st (bank j) = overlay (List.replicate g false) (σ.st (bank j))) ∧ (∀ j, τ.sh (bank j) = 0) ∧
      τ.st G = List.replicate g true ∧ τ.sh G = 0 ∧
      (∀ i, (∀ j, bank j ≠ i) → i ≠ G → τ.st i = σ.st i ∧ τ.sh i = σ.sh i) ∧ τ.val = σ.val ∧ τ.cell = σ.cell := by
  set tmap := Fin.addCases (motive := fun _ => Fin (ns + 1)) bank (fun _ : Fin 1 => G) with htmap
  have hinj' : Function.Injective tmap := bankG_injective bank hinj G hG
  have hL' : ∀ j, tmap j ≠ L := by
    intro j
    refine Fin.addCases (fun j' => ?_) (fun _ => ?_) j
    · simp only [htmap, Fin.addCases_left]; exact hL j'
    · simp only [htmap, Fin.addCases_right]; exact hGL
  have htin : (fun j => σ.st (tmap j)) = Fin.addCases (motive := fun _ => List Bool) (fun j => σ.st (bank j))
      (fun _ : Fin 1 => List.replicate g true) := by
    funext j
    refine Fin.addCases (fun j' => ?_) (fun _ => ?_) j
    · simp only [htmap, Fin.addCases_left]
    · simp only [htmap, Fin.addCases_right, hGst]
  have hstep := eraseStep t g (fun j => σ.st (bank j))
  rw [← htin] at hstep
  have h0' : ∀ j, σ.sh (tmap j) = 0 := by
    intro j
    refine Fin.addCases (fun j' => ?_) (fun _ => ?_) j
    · simp only [htmap, Fin.addCases_left]; exact h0 j'
    · simp only [htmap, Fin.addCases_right]; exact hGsh
  obtain ⟨τ, e, hd⟩ := WXExec.machZ_ex cap hinj' hL' σ hstep h0' hLst hLsh hcap
  refine ⟨τ, e, fun j => ?_, fun j => ?_, ?_, ?_, fun i hi hiG => ?_, hd.val, hd.cell⟩
  · have := hd.st (Fin.castAdd 1 j)
    simpa only [htmap, Fin.addCases_left] using this
  · have := hd.sh (Fin.castAdd 1 j)
    simpa only [htmap, Fin.addCases_left] using this
  · have := hd.st (Fin.natAdd t (0 : Fin 1))
    simpa only [htmap, Fin.addCases_right] using this
  · have := hd.sh (Fin.natAdd t (0 : Fin 1))
    simpa only [htmap, Fin.addCases_right] using this
  · refine hd.other i (fun j => ?_)
    refine Fin.addCases (fun j' => ?_) (fun _ => ?_) j
    · simp only [htmap, Fin.addCases_left]; exact hi j'
    · simp only [htmap, Fin.addCases_right]; exact fun h => hiG h.symm

/-- After the erase, a stream that read `0` from position `g` on reads `0` everywhere. -/
theorem blank_overlay (g : ℕ) (l : List Bool) (hl : ∀ q, g ≤ q → readTapeBit l q = false) :
    NearCubicGates.Close.Worker.Blank (overlay (List.replicate g false) l) := by
  intro q
  unfold overlay readTapeBit
  by_cases hq : q < g
  · rw [List.getD_append _ _ _ _ (by simpa using hq)]
    simp [hq]
  · rw [List.getD_append_right _ _ _ _ (by simp; omega)]
    have := hl q (by omega)
    unfold readTapeBit at this
    simp only [List.length_replicate, List.getD_eq_getElem?_getD, List.getElem?_drop] at this ⊢
    rw [show g + (q - g) = q by omega, this]

end NearQuarticWires.Control
