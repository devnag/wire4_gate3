import Proof.Quartic.StageNativeHeader.EmitBase

/-!
# The emission: numbers at depth three, repeated phases, the register arithmetic

Paper: `lem:print`, paper/paper.tex.

`numPhase`: a register value `v` is written as `marks (natWord v)` on an empty scratch stream (`writeNatM`), rewound,
and read back two cells at a time, appending `natWord v` at depth three to the accumulator. `repEmit`: a counted
loop of a phase appending the same word. `qPhase` computes `q = d + 2p + 3` (twice), `uPhase` computes `U = 2^d`
by `d` doublings, and `sqPhase` appends `U²` ones at depth two by `U` rounds of `U`.
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
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (addTo addTo_spec dbl dbl_spec)
open NearQuarticWires.Control

variable (cap : ℕ)

theorem emitted_setv (σ : WState hns hnr) (x : Fin hnr) (v : ℕ) (hx : x ≠ eOP) :
    Emitted σ (σ.setv x v) [] [x] [] :=
  ⟨by simp, by simp, by simp [Function.update_of_ne (Ne.symm hx)], fun y hy _ => by
    have hyx : y ≠ x := fun h => hy (by simp [h])
    simp [Function.update_of_ne hyx], fun _ _ _ => rfl, fun _ _ _ => rfl⟩

/-! ## A number at depth three -/

/-- Write `natWord v` (`v` in `R 0`) on `z`, rewind, read back at depth three. -/
noncomputable def numP (z : Fin (hns + 1)) (R : Fin 8 ↪ Fin hnr) : WM hns hnr :=
  .seq (writeNatM z R) (.seq (WM.rewind z (R 7)) (copyP z))

/-- The cost of `numP` for a value `v` of at most `ℓ` bits. -/
def numCost (v : ℕ) : ℕ := (natBitLength v + 10) * (100 * v + 200) + 400 * (natBitLength v + 1) + 10

theorem numPhase (z : Fin (hns + 1)) (hz : z ≠ sACC) (R : Fin 8 ↪ Fin hnr) (h7O : R 7 ≠ eOP) (h7S : R 7 ≠ eSC)
    (σ : WState hns hnr) (hzs : σ.st z = []) (hzh : σ.sh z = 0) (h1 : σ.val (R 1) = 0) (h2 : σ.val (R 2) = 0)
    (h3 : σ.val (R 3) = 0) (h4 : σ.val (R 4) = 0) (h5 : σ.val (R 5) = 0) (h6 : σ.val (R 6) = 0)
    (h7 : σ.val (R 7) = 0) (ho : σ.sh sACC = (σ.st sACC).length)
    (hc : σ.val (R 0) + 6 * natBitLength (σ.val (R 0)) + 6 ≤ cap)
    (hcm : 4 * natBitLength (σ.val (R 0)) + 2 ≤ cap)
    (hco : σ.val eOP + 8 * (RepairRepresentation.natWord (σ.val (R 0))).length ≤ cap)
    (hsc : σ.val eSC + 2 * (RepairRepresentation.natWord (σ.val (R 0))).length < cap + 1) :
    ∃ τ, WExec cap (numP z R) σ τ (numCost (σ.val (R 0))) ∧
      Emitted σ τ ((RepairRepresentation.natWord (σ.val (R 0))).flatMap deep3) [R 7, eSC] [z] ∧
      τ.val eSC = σ.val eSC + 2 * (RepairRepresentation.natWord (σ.val (R 0))).length := by
  set v := σ.val (R 0) with hv
  set w := RepairRepresentation.natWord v with hw
  have hwl : w.length = 2 * natBitLength v + 1 := by
    rw [hw]; exact NearCubicGates.Close.Cells.natWord_length v
  have e1 := writeNatM_spec cap z R σ h1 h2 h3 h4 h5 h6 (by rw [hzh, hzs]; rfl) (by rw [h7]; omega)
  set σ1 := appendO σ z (R 7) (marks w) with hσ1
  have hm : (marks w).length = 2 * w.length := NearCubicWires.RepairOrdinary.Streaming.marks_length w
  have s1 : σ1.st z = marks w := by simp [hσ1, appendO, hzs]
  have v1 : σ1.val (R 7) = (marks w).length := by simp [hσ1, appendO, h7]
  have e2 := wrewind_spec cap z (R 7) (marks w).length σ1 v1 (by rw [v1, hm, hwl]; omega)
  set σ2 := (σ1.setv (R 7) 0).seth z (σ1.sh z - (marks w).length) with hσ2
  have s2 : σ2.st z = [] ++ marks w ++ [] := by simp [hσ2, s1]
  have sh2 : σ2.sh z = ([] : List Bool).length := by simp [hσ2, hσ1, appendO, hzh]
  have hz' : sACC ≠ z := Ne.symm hz
  have ho2 : σ2.sh sACC = (σ2.st sACC).length := by
    simp [hσ2, hσ1, appendO, Function.update_of_ne hz', ho]
  have op2 : σ2.val eOP = σ.val eOP := by
    simp [hσ2, hσ1, appendO, Function.update_of_ne (Ne.symm h7O)]
  have sc2 : σ2.val eSC = σ.val eSC := by
    simp [hσ2, hσ1, appendO, Function.update_of_ne (Ne.symm h7S)]
  obtain ⟨τ, e3, m3, -, -, sc3⟩ := copyPhase cap z hz w [] [] rfl σ2 s2 sh2 ho2 (by rw [op2]; omega)
    (by rw [sc2]; omega)
  refine ⟨τ, WExec.mono (WExec.seq e1 (WExec.seq e2 e3)) ?_, ?_, by rw [sc3, sc2]⟩
  · unfold numCost; rw [hm, hwl]; nlinarith
  · have m12 : Emitted σ σ2 [] [R 7, eSC] [z] := by
      refine ⟨?_, ?_, op2, ?_, ?_, ?_⟩
      · simp [hσ2, hσ1, appendO, Function.update_of_ne hz']
      · simp [hσ2, hσ1, appendO, Function.update_of_ne hz']
      · intro x hx _
        have hx7 : x ≠ R 7 := fun h => hx (by simp [h])
        simp [hσ2, hσ1, appendO, Function.update_of_ne hx7]
      · intro j hj _
        have hjz : j ≠ z := fun h => hj (by simp [h])
        simp [hσ2, hσ1, appendO, Function.update_of_ne hjz]
      · intro j hj _
        have hjz : j ≠ z := fun h => hj (by simp [h])
        simp [hσ2, hσ1, appendO, Function.update_of_ne hjz]
    exact (m12.trans (m3.weaken (fun x hx => by simp at hx ⊢; simp [hx]) (fun j hj => hj))).equ (by simp)

/-! ## Repetition of a phase -/

/-- **A counted loop of a phase appending `u`**, with an invariant indexed by the number of rounds done. -/
theorem repEmit (K : Fin hnr) (hK : K ≠ eOP) (P : WM hns hnr) (u : List Bool) (c : ℕ) (L : List (Fin hnr))
    (S : List (Fin (hns + 1))) (hKL : K ∉ L) (m : ℕ) (Pre : ℕ → WState hns hnr → Prop)
    (hset : ∀ i σ x, Pre i σ → Pre i (σ.setv K x))
    (hP : ∀ i < m, ∀ σ, Pre i σ → σ.sh sACC = (σ.st sACC).length → σ.val eOP + u.length ≤ cap →
      ∃ τ, WExec cap P σ τ c ∧ Emitted σ τ u L S ∧ Pre (i + 1) τ) :
    ∀ σ, σ.val K = m → Pre 0 σ → σ.sh sACC = (σ.st sACC).length → σ.val eOP + m * u.length ≤ cap → m ≤ cap →
      ∃ τ, WExec cap (runLoop K P) σ τ (m * (c + 4) + 1) ∧ Emitted σ τ (List.replicate m u).flatten (K :: L) S ∧
        Pre m τ ∧ τ.val K = 0 := by
  have key : ∀ j i, i + j = m → ∀ σ, σ.val K = j → Pre i σ → σ.sh sACC = (σ.st sACC).length →
      σ.val eOP + j * u.length ≤ cap → j ≤ cap →
      ∃ τ, WExec cap (runLoop K P) σ τ (j * (c + 4) + 1) ∧ Emitted σ τ (List.replicate j u).flatten (K :: L) S ∧
        Pre m τ ∧ τ.val K = 0 := by
    intro j
    induction j with
    | zero =>
      intro i hi σ hK0 hp _ _ _
      rw [Nat.add_zero] at hi; subst hi
      exact ⟨σ, WExec.mono (WExec.whrF hK0) (by omega), (Emitted.refl σ _ _).equ (by simp), hp, hK0⟩
    | succ j ih =>
      intro i hi σ hKj hp ho hc hjc
      have e1 := WExec.dec (cap := cap) K σ (by omega)
      set σ1 := σ.setv K (σ.val K - 1) with hσ1
      have m1 : Emitted σ σ1 [] (K :: L) S :=
        (emitted_setv σ K _ hK).weaken (fun x hx => by simp at hx; simp [hx]) (fun _ h => by simp at h)
      obtain ⟨τ1, e2, m2, p2⟩ := hP i (by omega) σ1 (hset i σ _ hp) (by simpa [hσ1] using ho)
        (by simp [hσ1, Function.update_of_ne (Ne.symm hK)]; nlinarith)
      have k1 : τ1.val K = j := by
        rw [m2.val K hKL hK]; simp [hσ1, hKj]
      have ho1 : τ1.sh sACC = (τ1.st sACC).length := by
        rw [m2.acch, m2.acc, List.length_append]; simp [hσ1, ho]
      obtain ⟨τ, e3, m3, p3, k3⟩ := ih (i + 1) (by omega) τ1 k1 p2 ho1
        (by rw [m2.op]; simp [hσ1, Function.update_of_ne (Ne.symm hK)]; nlinarith) (by omega)
      refine ⟨τ, WExec.mono (WExec.whrT (by rw [hKj]; omega) (WExec.seq e1 e2) e3) (by ring_nf; omega), ?_, p3, k3⟩
      have := (m1.trans (m2.weaken (fun x hx => List.mem_cons_of_mem _ hx) (fun _ h => h))).trans m3
      exact this.equ (by simp [List.replicate_succ])
  intro σ hK0 hp ho hc hmc
  exact key m 0 (by omega) σ hK0 hp ho hc hmc

/-! ## `q = d + 2p + 3` -/

/-- `rQ := d + 2p + 3` and its copy `rV`. -/
noncomputable def qP : WM hns hnr := .seq (addTo rD rQ rTmp) (.seq (addTo rP rQ rTmp) (.seq (addTo rP rQ rTmp)
  (.seq (.inc rQ) (.seq (.inc rQ) (.seq (.inc rQ) (addTo rQ rV rTmp))))))

theorem qPhase (σ : WState hns hnr) (d p : ℕ) (hd : σ.val rD = d) (hp : σ.val rP = p) (hQ : σ.val rQ = 0)
    (hV : σ.val rV = 0) (hT : σ.val rTmp = 0) (hcap : 2 * (d + 2 * p + 3) + 1 ≤ cap) :
    ∃ τ, WExec cap qP σ τ (72 * (d + 2 * p + 3) + 30) ∧ Emitted σ τ [] [rQ, rV] [] ∧
      τ.val rQ = d + 2 * p + 3 ∧ τ.val rV = d + 2 * p + 3 := by
  have e1 := addTo_spec cap rD rQ rTmp (by decide) (by decide) (by decide) σ hT (by omega) (by omega)
  set σ1 := σ.setv rQ (σ.val rQ + σ.val rD) with hσ1
  have e2 := addTo_spec cap rP rQ rTmp (by decide) (by decide) (by decide) σ1 (by simp (config := { decide := true }) [hσ1, hT])
    (by simp (config := { decide := true }) [hσ1, hp]; omega) (by simp (config := { decide := true }) [hσ1, hp, hQ, hd]; omega)
  set σ2 := σ1.setv rQ (σ1.val rQ + σ1.val rP) with hσ2
  have e3 := addTo_spec cap rP rQ rTmp (by decide) (by decide) (by decide) σ2 (by simp (config := { decide := true }) [hσ2, hσ1, hT])
    (by simp (config := { decide := true }) [hσ2, hσ1, hp]; omega) (by simp (config := { decide := true }) [hσ2, hσ1, hp, hQ, hd]; omega)
  set σ3 := σ2.setv rQ (σ2.val rQ + σ2.val rP) with hσ3
  have q3 : σ3.val rQ = d + 2 * p := by simp (config := { decide := true }) [hσ3, hσ2, hσ1, hp, hQ, hd]; ring
  have e4 := WExec.inc (cap := cap) rQ σ3 (by rw [q3]; omega)
  set σ4 := σ3.setv rQ (σ3.val rQ + 1) with hσ4
  have e5 := WExec.inc (cap := cap) rQ σ4 (by simp (config := { decide := true }) [hσ4, q3]; omega)
  set σ5 := σ4.setv rQ (σ4.val rQ + 1) with hσ5
  have e6 := WExec.inc (cap := cap) rQ σ5 (by simp (config := { decide := true }) [hσ5, hσ4, q3]; omega)
  set σ6 := σ5.setv rQ (σ5.val rQ + 1) with hσ6
  have q6 : σ6.val rQ = d + 2 * p + 3 := by simp (config := { decide := true }) [hσ6, hσ5, hσ4, q3]
  have t6 : σ6.val rTmp = 0 := by simp (config := { decide := true }) [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, hT]
  have e7 := addTo_spec cap rQ rV rTmp (by decide) (by decide) (by decide) σ6 t6 (by rw [q6]; omega)
    (by rw [q6]; simp (config := { decide := true }) [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, hV]; omega)
  refine ⟨_, WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6 e7))))))
    ?_, ?_, ?_, ?_⟩
  · simp (config := { decide := true }) [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, hd, hp, hQ]; nlinarith
  · refine ⟨by simp (config := { decide := true }) [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1], by simp (config := { decide := true }) [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1],
      by simp (config := { decide := true }) [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1], fun x hx _ => ?_, fun _ _ _ => rfl, fun _ _ _ => rfl⟩
    have h1 : x ≠ rQ := fun h => hx (by simp (config := { decide := true }) [h])
    have h2 : x ≠ rV := fun h => hx (by simp (config := { decide := true }) [h])
    simp (config := { decide := true }) [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_of_ne h1, Function.update_of_ne h2]
  · simp (config := { decide := true }) [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, hd, hp, hQ]; ring
  · simp (config := { decide := true }) [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, hd, hp, hQ, hV]; ring

end NearQuarticWires.StageNativeHeader
