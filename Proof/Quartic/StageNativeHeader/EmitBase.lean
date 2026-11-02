import Proof.Quartic.StageNativeHeader.EmitReady

/-!
# The emission of the native table request: registers and phases

Paper: `lem:print`, paper/paper.tex.

The emission appends the marked native table request to the accumulator `sACC` piece by piece. `Emitted σ τ u L S`:
from `σ` to `τ`, `u` is appended to `sACC` (its head and its counter `eOP` advance by `|u|`), only the registers of
`L` and the streams of `S` change. The phases: a number at depth three (`numPhase`: written on a scratch stream,
rewound, read back two cells at a time), a marked stream at depth three (`copyPhase`), fixed bits (`listPhase`) and
a unary field at depth two (`unaryPhase`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearQuarticWires.StageNativeHeader

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close.Recovery.HTParts (adv pairLoop pairLoop_spec Emits emits_none)
open NearQuarticWires.Control

/-! ## Registers of the emission -/

/-- The counter of the accumulator. -/
def eOP : Fin hnr := 30
/-- The cell counter of the read-back loops. -/
def eSC : Fin hnr := 31
/-- The counters of the three number streams. -/
def eOZd : Fin hnr := 32
def eOZp : Fin hnr := 33
def eOZG : Fin hnr := 34
/-- The outer and inner counters of the `U²` field. -/
def eK2 : Fin hnr := 35
def eK3 : Fin hnr := 37

/-- The registers of `writeNatM` printing `v` with the counter `c` (scratch `5 … 10`). -/
def wR (v c : Fin hnr) (h : Function.Injective ![v, 5, 6, 7, 8, 9, 10, c]) : Fin 8 ↪ Fin hnr :=
  ⟨![v, 5, 6, 7, 8, 9, 10, c], h⟩

/-- The registers printing `d`, `p` and `G`. -/
def wRd : Fin 8 ↪ Fin hnr := wR rD eOZd (by decide)
def wRp : Fin 8 ↪ Fin hnr := wR rP eOZp (by decide)
def wRG : Fin 8 ↪ Fin hnr := wR rG eOZG (by decide)

/-! ## The effect of a phase -/

variable (cap : ℕ)

/-- From `σ` to `τ`: `u` appended to `sACC` (head and counter `eOP` advanced), only the registers of `L` and the
streams of `S` changed. -/
structure Emitted (σ τ : WState hns hnr) (u : List Bool) (L : List (Fin hnr)) (S : List (Fin (hns + 1))) : Prop where
  acc : τ.st sACC = σ.st sACC ++ u
  acch : τ.sh sACC = σ.sh sACC + u.length
  op : τ.val eOP = σ.val eOP + u.length
  val : ∀ x, x ∉ L → x ≠ eOP → τ.val x = σ.val x
  st : ∀ j, j ∉ S → j ≠ sACC → τ.st j = σ.st j
  sh : ∀ j, j ∉ S → j ≠ sACC → τ.sh j = σ.sh j

namespace Emitted

variable {σ τ ρ : WState hns hnr} {u u' : List Bool} {L L' : List (Fin hnr)} {S S' : List (Fin (hns + 1))}

theorem refl (σ : WState hns hnr) (L : List (Fin hnr)) (S : List (Fin (hns + 1))) : Emitted σ σ [] L S :=
  ⟨by simp, by simp, by simp, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

theorem trans (h1 : Emitted σ τ u L S) (h2 : Emitted τ ρ u' L S) : Emitted σ ρ (u ++ u') L S :=
  ⟨by rw [h2.acc, h1.acc, List.append_assoc], by rw [h2.acch, h1.acch, List.length_append]; ring,
    by rw [h2.op, h1.op, List.length_append]; ring, fun x hx ho => (h2.val x hx ho).trans (h1.val x hx ho),
    fun j hj ha => (h2.st j hj ha).trans (h1.st j hj ha), fun j hj ha => (h2.sh j hj ha).trans (h1.sh j hj ha)⟩

theorem weaken (h : Emitted σ τ u L S) (hL : ∀ x ∈ L, x ∈ L') (hS : ∀ j ∈ S, j ∈ S') : Emitted σ τ u L' S' :=
  ⟨h.acc, h.acch, h.op, fun x hx ho => h.val x (fun h' => hx (hL x h')) ho,
    fun j hj ha => h.st j (fun h' => hj (hS j h')) ha, fun j hj ha => h.sh j (fun h' => hj (hS j h')) ha⟩

theorem equ (h : Emitted σ τ u L S) (hu : u = u') : Emitted σ τ u' L S := hu ▸ h

end Emitted

theorem sACC_ne_sZd : sACC ≠ sZd := sne (by simp [sACC, sZd, strm])
theorem sACC_ne_sZp : sACC ≠ sZp := sne (by simp [sACC, sZp, strm])
theorem sACC_ne_sZG : sACC ≠ sZG := sne (by simp [sACC, sZG, strm])
theorem sACC_ne_sY : sACC ≠ sY := sne (by simp [sACC, sY, strm])
theorem sACC_ne_sIN : sACC ≠ sIN := sne (by simp [sACC, sIN, strm])

/-! ## Fixed bits -/

/-- Append the bits of `l` to the accumulator. -/
theorem listPhase (l : List Bool) (σ : WState hns hnr) (ho : σ.sh sACC = (σ.st sACC).length)
    (hc : σ.val eOP + l.length ≤ cap) :
    ∃ τ, WExec cap (emitList sACC eOP l) σ τ (8 * l.length) ∧ Emitted σ τ l [] [] := by
  refine ⟨_, emitList_exec cap sACC eOP l σ ho hc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [appendO]
  · simp [appendO]
  · simp [appendO]
  · intro x _ hx; simp [appendO, Function.update_of_ne hx]
  · intro j _ hj; simp [appendO, Function.update_of_ne hj]
  · intro j _ hj; simp [appendO, Function.update_of_ne hj]

/-! ## A unary field at depth two -/

/-- `m` ones at depth two, `m` the value of `K` (left at `0`). -/
noncomputable def unaryP (K : Fin hnr) : WM hns hnr := runLoop K (emitList sACC eOP [true, true, true, true])

theorem unaryPhase (K : Fin hnr) (hK : K ≠ eOP) (m : ℕ) (σ : WState hns hnr) (hm : σ.val K = m)
    (ho : σ.sh sACC = (σ.st sACC).length) (hc : σ.val eOP + 4 * m ≤ cap) (hmc : m ≤ cap) :
    ∃ τ, WExec cap (unaryP K) σ τ (m * 36 + 1) ∧ Emitted σ τ (unary2 m) [K] [] ∧ τ.val K = 0 := by
  have e := runLoop_exec cap K eOP sACC hK (emitList sACC eOP [true, true, true, true]) [true, true, true, true] 32
    (fun τ ho' hc' => by simpa using emitList_exec cap sACC eOP [true, true, true, true] τ ho' hc') m σ hm ho
    (by simpa [Nat.mul_comm] using hc) hmc
  refine ⟨_, e, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, by simp⟩
  · simp [appendO, unary2]
  · simp [appendO, unary2]
  · simp [appendO, Function.update_of_ne (Ne.symm hK), unary2]
  · intro x hx hxo
    have hxK : x ≠ K := fun h => hx (by simp [h])
    simp [appendO, Function.update_of_ne hxK, Function.update_of_ne hxo]
  · intro j _ hj; simp [appendO, Function.update_of_ne hj]
  · intro j _ hj; simp [appendO, Function.update_of_ne hj]

/-! ## A marked stream at depth three -/

/-- Read back the marked word on `src`, writing each bit at depth three. -/
noncomputable def copyP (src : Fin (hns + 1)) : WM hns hnr := pairLoop src eSC (fun _ => WM.skip) (emitDeep sACC eOP)

theorem copyPhase (src : Fin (hns + 1)) (hsrc : src ≠ sACC) (w pre rest : List Bool) (hrest : rest.headD false = false)
    (σ : WState hns hnr) (hst : σ.st src = pre ++ marks w ++ rest) (hsh : σ.sh src = pre.length)
    (ho : σ.sh sACC = (σ.st sACC).length) (hc : σ.val eOP + 8 * w.length ≤ cap)
    (hsc : σ.val eSC + 2 * w.length < cap + 1) :
    ∃ τ, WExec cap (copyP src) σ τ (w.length * 81 + 1) ∧ Emitted σ τ (w.flatMap deep3) [eSC] [src] ∧
      τ.st src = σ.st src ∧ τ.sh src = σ.sh src + 2 * w.length ∧ τ.val eSC = σ.val eSC + 2 * w.length := by
  have hlen : (w.flatMap fun b => ([] : List Bool) ++ deep3 b).length = 8 * w.length := by
    induction w with
    | nil => simp
    | cons b w ih => simp only [List.flatMap_cons, List.length_append, ih, List.length_cons]; simp [deep3]; ring
  have e := pairLoop_spec cap hsrc (show eOP ≠ eSC by decide) (emits_none cap (dst := sACC) (OP := eOP))
    (emits_deep cap sACC eOP) rest hrest w pre σ hst hsh ho (by rw [hlen]; exact hc) hsc
  have hfm : (w.flatMap fun b => ([] : List Bool) ++ deep3 b) = w.flatMap deep3 := by simp
  rw [hfm] at e
  refine ⟨_, WExec.mono e (by omega), ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · simp
  · rw [NearCubicGates.Close.Recovery.HTParts.adv_sh_dst hsrc]
  · rw [NearCubicGates.Close.Recovery.HTParts.adv_val_OP (show eOP ≠ eSC by decide)]
  · intro x hx hxo
    exact NearCubicGates.Close.Recovery.HTParts.adv_val_other _ _ _ x hxo (fun h => hx (by simp [h]))
  · intro j _ hj; exact NearCubicGates.Close.Recovery.HTParts.adv_st_other _ _ _ j hj
  · intro j hj hja
    exact NearCubicGates.Close.Recovery.HTParts.adv_sh_other _ _ _ j hja (fun h => hj (by simp [h]))
  · exact NearCubicGates.Close.Recovery.HTParts.adv_st_src hsrc _ _ _
  · rw [NearCubicGates.Close.Recovery.HTParts.adv_sh_src]
  · rw [NearCubicGates.Close.Recovery.HTParts.adv_val_SC]

end NearQuarticWires.StageNativeHeader
