import Proof.Quartic.StageNativeMiddleMap.Layout
import Proof.Wire_3_5.PrimTReadEq

set_option autoImplicit false

namespace NearQuarticWires.StageNativeMiddleMap

open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimT.ReadEq

/-- `lem:print`, paper/paper.tex: ordinary
register-only formatting transports across read-equivalent retained
sources while preserving exact bytes on an initially equal output tape. -/
theorem wexec_sim_exact {ns nr cap : ℕ} {P : WM ns nr} {σ τ : WState ns nr} {n : ℕ} (h : WExec cap P σ τ n) (OUT : Fin (ns+1)) :
    ∀ σ' : WState ns nr, SimW σ σ' → σ.st OUT=σ'.st OUT →
      ∃ τ', WExec cap P σ' τ' n ∧ SimW τ τ' ∧ τ.st OUT=τ'.st OUT := by
  induction h with
  | skip σ => exact fun σ' hs hO => ⟨σ', WExec.skip σ', hs, hO⟩
  | inc r σ hv =>
    intro σ' hs hO
    refine ⟨σ'.setv r (σ'.val r + 1), WExec.inc r σ' (by rw [hs.val]; exact hv), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · simp [hs.sh]
    · simp [hs.val]
    · simp [hs.cell]
    · intro i; simpa using hs.st i
    · simpa only [WState.setv_st] using hO
  | dec r σ hv =>
    intro σ' hs hO
    refine ⟨σ'.setv r (σ'.val r - 1), WExec.dec r σ' (by rw [hs.val]; exact hv), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · simp [hs.sh]
    · simp [hs.val]
    · simp [hs.cell]
    · intro i; simpa using hs.st i
    · simpa only [WState.setv_st] using hO
  | fwd i σ =>
    intro σ' hs hO
    refine ⟨σ'.seth i (σ'.sh i + 1), WExec.fwd i σ', ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · simp [hs.sh]
    · simp [hs.val]
    · simp [hs.cell]
    · intro j; simpa using hs.st j
    · exact hO
  | bwd i σ =>
    intro σ' hs hO
    refine ⟨σ'.seth i (σ'.sh i - 1), WExec.bwd i σ', ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · simp [hs.sh]
    · simp [hs.val]
    · simp [hs.cell]
    · intro j; simpa using hs.st j
    · exact hO
  | wr i b σ =>
    intro σ' hs hO
    refine ⟨σ'.sets i (writeTapeBit (σ'.st i) (σ'.sh i) b), WExec.wr i b σ', ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · simp [hs.sh]
    · simp [hs.val]
    · simp [hs.cell]
    · intro j
      by_cases hj : j = i
      · subst hj
        simp only [WState.sets_st, Function.update_self]
        rw [hs.sh]
        exact rdEq_write (hs.st j) _ b
      · simp only [WState.sets_st, Function.update_of_ne hj]
        exact hs.st j
    · by_cases hi : OUT=i
      · subst hi
        simp only [WState.sets_st,Function.update_self]
        rw [hs.sh,hO]
      · simpa only [WState.sets_st,Function.update_of_ne hi] using hO
  | setc v σ =>
    intro σ' hs hO
    refine ⟨σ'.setc v, WExec.setc v σ', ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · simp [hs.sh]
    · simp [hs.val]
    · simp
    · intro j; simpa using hs.st j
    · exact hO
  | seq _ _ ih1 ih2 =>
    intro σ' hs hO
    obtain ⟨τ1, e1, s1, h1⟩ := ih1 σ' hs hO
    obtain ⟨τ2, e2, s2, h2⟩ := ih2 τ1 s1 h1
    exact ⟨τ2, WExec.seq e1 e2, s2, h2⟩
  | ifrT hv _ ih =>
    intro σ' hs hO
    obtain ⟨τ1, e1, s1, h1⟩ := ih σ' hs hO
    exact ⟨τ1, WExec.ifrT (by rw [hs.val]; exact hv) e1, s1, h1⟩
  | ifrF hv _ ih =>
    intro σ' hs hO
    obtain ⟨τ1, e1, s1, h1⟩ := ih σ' hs hO
    exact ⟨τ1, WExec.ifrF (by rw [hs.val]; exact hv) e1, s1, h1⟩
  | ifsT hb _ ih =>
    intro σ' hs hO
    obtain ⟨τ1, e1, s1, h1⟩ := ih σ' hs hO
    exact ⟨τ1, WExec.ifsT (by rw [hs.bit]; exact hb) e1, s1, h1⟩
  | ifsF hb _ ih =>
    intro σ' hs hO
    obtain ⟨τ1, e1, s1, h1⟩ := ih σ' hs hO
    exact ⟨τ1, WExec.ifsF (by rw [hs.bit]; exact hb) e1, s1, h1⟩
  | whrF hv =>
    intro σ' hs hO
    exact ⟨σ', WExec.whrF (by rw [hs.val]; exact hv), hs, hO⟩
  | whrT hv _ _ ih1 ih2 =>
    intro σ' hs hO
    obtain ⟨τ1, e1, s1, h1⟩ := ih1 σ' hs hO
    obtain ⟨τ2, e2, s2, h2⟩ := ih2 τ1 s1 h1
    exact ⟨τ2, WExec.whrT (by rw [hs.val]; exact hv) e1 e2, s2, h2⟩
  | whsF hb =>
    intro σ' hs hO
    exact ⟨σ', WExec.whsF (by rw [hs.bit]; exact hb), hs, hO⟩
  | whsT hb _ _ ih1 ih2 =>
    intro σ' hs hO
    obtain ⟨τ1, e1, s1, h1⟩ := ih1 σ' hs hO
    obtain ⟨τ2, e2, s2, h2⟩ := ih2 τ1 s1 h1
    exact ⟨τ2, WExec.whsT (by rw [hs.bit]; exact hb) e1 e2, s2, h2⟩
  | mono _ hn ih =>
    intro σ' hs hO
    obtain ⟨τ1, e1, s1, h1⟩ := ih σ' hs hO
    exact ⟨τ1, WExec.mono e1 hn, s1, h1⟩


end NearQuarticWires.StageNativeMiddleMap
