import Proof.Quartic.Control.Frame
import Proof.Wire_3_5.SeedFixGreedy

/-!
# The `S` rounds of the seed-fixing loop

Paper: Step 3 of `sec:algorithm`, paper/paper.tex: `S` rounds from the empty prefix, each appending
the bit of the child of smaller value; the seed is `greedyLoop S R = (greedyStep R)^[S] []` (imported from
`Proof.Wire_3_5.SeedFixGreedy`). `prop:time`: `2S` child evaluations.

`roundsP` runs `roundP` while the round counter `K` is positive, decrementing it first (`Runs.count`, imported from
`Proof.Gates.WordPrograms.Hoare`). `rounds_exec`: from the round state of the empty prefix with `K = S`, the loop
reaches a state that reads like the round state of the greedy seed with `K = 0`, in `S (roundCost + 4) + 1` steps.
-/

set_option autoImplicit false

namespace NearQuarticWires.Control

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.PrimT.ReadEq NearCubicGates.Close.CheckedPCPP
open NearCubicWires.WireExponent3_5.SeedFix (greedyStep greedyLoop)

/-- The round counter. -/
def rK : Fin lnr := ⟨11, by simp only [lnr]; omega⟩

/-- **The rounds**: while `K > 0`, `K := K − 1` and one round. -/
noncomputable def roundsP (p : Program) : WMX (lns p.tapeCount) lnr := .whr rK (.seq (WMX.dec rK) (roundP p))

theorem greedy_iterate_length (R : List Bool → ℤ) (k : ℕ) : ((greedyStep R)^[k] []).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', greedyStep, List.length_append, ih]; rfl

theorem simW_setv {ns nr : ℕ} {σ σ' : WState ns nr} (h : SimW σ σ') (r : Fin nr) (v : ℕ) :
    SimW (σ.setv r v) (σ'.setv r v) :=
  ⟨by simp [h.sh], by simp [h.val], by simp [h.cell], fun i => by simpa using h.st i⟩

theorem setv_setv {ns nr : ℕ} (σ : WState ns nr) (r : Fin nr) (a b : ℕ) : (σ.setv r a).setv r b = σ.setv r b := by
  refine WState.eq rfl rfl ?_ rfl
  funext q; by_cases hq : q = r
  · subst hq; simp
  · simp [Function.update_of_ne hq]

theorem roundSt_setv {t : ℕ} (ρ : WState (lns t) lnr) (π : List Bool) (v : ℕ) :
    (roundSt ρ π).setv rK v = roundSt (ρ.setv rK v) π := rfl

theorem loopReady_setv {t : ℕ} {ρ : WState (lns t) lnr} {w : List Bool} (h : LoopReady t ρ w) (v : ℕ) :
    LoopReady t (ρ.setv rK v) w where
  inp := h.inp
  inph := h.inph
  ph := h.ph
  ruler := h.ruler
  rulerh := h.rulerh
  bA := h.bA
  bAh := h.bAh
  bB := h.bB
  bBh := h.bBh
  tA := h.tA
  tAh := h.tAh
  gA := h.gA
  gAh := h.gAh
  tB := h.tB
  tBh := h.tBh
  gB := h.gB
  gBh := h.gBh
  rs := fun i => by
    have : rS i ≠ rK := fun e => by have := congrArg Fin.val e; simp [rS, rK] at this; omega
    simp [Function.update_of_ne this, h.rs i]
  rg := fun i => by
    have : rG i ≠ rK := fun e => by have := congrArg Fin.val e; simp [rG, rK] at this; omega
    simp [Function.update_of_ne this, h.rg i]
  op := by simp [Function.update_of_ne (show rOP ≠ rK by decide), h.op]
  c := by simp [Function.update_of_ne (show rC ≠ rK by decide), h.c]

/-- **The `S` rounds.** With a child word function `f` whose requests `req π` (for the prefixes of length at most
`S`) have the input `w ++ frame π`, the value `R π` and a budget at most `B`, the rounds take a state that reads like
the round state of the empty prefix with `K = S` to a state that reads like the round state of the greedy seed
`greedyLoop S R` with `K = 0`. -/
theorem rounds_exec {Request : Type} {input : Request → List Bool} {Rv : Request → ℤ} {budget : Request → ℕ}
    (f : WordFunction Request input (fun r => NearCubicGates.Close.Interfaces.intWord (Rv r)) budget)
    (cap : ℕ) (ρ : WState (lns f.program.tapeCount) lnr) (w : List Bool) (hρ : LoopReady f.program.tapeCount ρ w)
    (S : ℕ) (R : List Bool → ℤ) (req : (π : List Bool) → π.length ≤ S → Request)
    (hreq : ∀ π h, input (req π h) = w ++ frame π ∧ Rv (req π h) = R π) (B : ℕ)
    (hB : ∀ π h, budget (req π h) ≤ B) (hcap : 10 * (w.length + S + B + 10) ≤ cap) (σ : WState _ lnr)
    (hσ : SimW (roundSt (ρ.setv rK S) []) σ) :
    ∃ τ, WXExec cap (roundsP f.program) σ τ (S * (roundCost w.length S B + 4) + 1) ∧
      SimW (roundSt (ρ.setv rK 0) (greedyLoop S R)) τ := by
  have hl := Runs.count (cap := cap) (K := rK) (body := roundP f.program) (roundCost w.length S B) S
    (fun k τ => SimW (roundSt (ρ.setv rK (S - k)) ((greedyStep R)^[k] [])) τ) (by omega)
    (by
      intro k hk τ hτ _
      set πk := (greedyStep R)^[k] [] with hπk
      have hlen : πk.length = k := greedy_iterate_length R k
      have h0 : (πk ++ [false]).length ≤ S := by simp [hlen]; omega
      have h1 : (πk ++ [true]).length ≤ S := by simp [hlen]; omega
      obtain ⟨τ0, e0, s0⟩ := round_exec f cap (ρ.setv rK (S - k - 1)) w πk (loopReady_setv hρ _)
        (req _ h0) (req _ h1) (hreq _ h0).1 (hreq _ h1).1 B (hB _ h0) (hB _ h1) (by rw [hlen]; omega)
      have hsim : SimW (roundSt (ρ.setv rK (S - k - 1)) πk) (τ.setv rK (S - k - 1)) := by
        have := simW_setv hτ rK (S - k - 1)
        rwa [← roundSt_setv, setv_setv, roundSt_setv] at this
      obtain ⟨τ1, e1, s1⟩ := wxexec_sim e0 _ hsim
      refine ⟨τ1, e1.mono ?_, ?_, ?_⟩
      · unfold roundCost; rw [hlen]; omega
      · have hstep : πk ++ [decide (Rv (req _ h1) < Rv (req _ h0))] = (greedyStep R)^[k + 1] [] := by
          rw [Function.iterate_succ_apply', ← hπk, greedyStep, (hreq _ h0).2, (hreq _ h1).2]
        rw [hstep] at s0
        rw [show S - (k + 1) = S - k - 1 by omega]
        exact SimW.trans s0 s1
      · rw [s1.val, s0.val]
        simp [roundSt])
    σ (by simpa using hσ) (by rw [hσ.val]; simp [roundSt])
  obtain ⟨τ, e, hτ, -⟩ := hl
  refine ⟨τ, e, ?_⟩
  simpa [greedyLoop] using hτ

end NearQuarticWires.Control
