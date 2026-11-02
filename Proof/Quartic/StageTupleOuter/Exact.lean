import Proof.Wire_3_5.PrimTReadEq

/-!
# Read-alike runs keep an exactly equal stream exactly equal

Paper: `lem:print`, paper/paper.tex.

`wexec_sim_eq`: if a word program runs from `σ`, and `σ'` reads like `σ` (`SimW`) and holds literally the same list on
one stream `o`, then the program runs from `σ'` in the same number of steps to a state reading like the result and
holding literally the same list on `o`. Reads agree everywhere and writes act on equal lists at equal heads.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageTupleOuter

open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq

variable {ns nr : ℕ}

/-- **Read-alike runs, one stream exact.** -/
theorem wexec_sim_eq {cap : ℕ} (o : Fin (ns + 1)) {P : WM ns nr} {σ τ : WState ns nr} {n : ℕ}
    (h : WExec cap P σ τ n) :
    ∀ σ' : WState ns nr, SimW σ σ' → σ'.st o = σ.st o →
      ∃ τ', WExec cap P σ' τ' n ∧ SimW τ τ' ∧ τ'.st o = τ.st o := by
  induction h with
  | skip σ => exact fun σ' hs he => ⟨σ', WExec.skip σ', hs, he⟩
  | inc r σ hv =>
    intro σ' hs he
    refine ⟨σ'.setv r (σ'.val r + 1), WExec.inc r σ' (by rw [hs.val]; exact hv), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · simp [hs.sh]
    · simp [hs.val]
    · simp [hs.cell]
    · intro i; simpa using hs.st i
    · simpa using he
  | dec r σ hv =>
    intro σ' hs he
    refine ⟨σ'.setv r (σ'.val r - 1), WExec.dec r σ' (by rw [hs.val]; exact hv), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · simp [hs.sh]
    · simp [hs.val]
    · simp [hs.cell]
    · intro i; simpa using hs.st i
    · simpa using he
  | fwd i σ =>
    intro σ' hs he
    refine ⟨σ'.seth i (σ'.sh i + 1), WExec.fwd i σ', ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · simp [hs.sh]
    · simp [hs.val]
    · simp [hs.cell]
    · intro j; simpa using hs.st j
    · simpa using he
  | bwd i σ =>
    intro σ' hs he
    refine ⟨σ'.seth i (σ'.sh i - 1), WExec.bwd i σ', ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · simp [hs.sh]
    · simp [hs.val]
    · simp [hs.cell]
    · intro j; simpa using hs.st j
    · simpa using he
  | wr i b σ =>
    intro σ' hs he
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
    · by_cases ho : o = i
      · subst ho
        simp only [WState.sets_st, Function.update_self]
        rw [he, hs.sh]
      · simp only [WState.sets_st, Function.update_of_ne ho]
        exact he
  | setc v σ =>
    intro σ' hs he
    refine ⟨σ'.setc v, WExec.setc v σ', ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · simp [hs.sh]
    · simp [hs.val]
    · simp
    · intro j; simpa using hs.st j
    · simpa using he
  | seq _ _ ih1 ih2 =>
    intro σ' hs he
    obtain ⟨τ1, e1, s1, h1⟩ := ih1 σ' hs he
    obtain ⟨τ2, e2, s2, h2⟩ := ih2 τ1 s1 h1
    exact ⟨τ2, WExec.seq e1 e2, s2, h2⟩
  | ifrT hv _ ih =>
    intro σ' hs he
    obtain ⟨τ1, e1, s1, h1⟩ := ih σ' hs he
    exact ⟨τ1, WExec.ifrT (by rw [hs.val]; exact hv) e1, s1, h1⟩
  | ifrF hv _ ih =>
    intro σ' hs he
    obtain ⟨τ1, e1, s1, h1⟩ := ih σ' hs he
    exact ⟨τ1, WExec.ifrF (by rw [hs.val]; exact hv) e1, s1, h1⟩
  | ifsT hb _ ih =>
    intro σ' hs he
    obtain ⟨τ1, e1, s1, h1⟩ := ih σ' hs he
    exact ⟨τ1, WExec.ifsT (by rw [hs.bit]; exact hb) e1, s1, h1⟩
  | ifsF hb _ ih =>
    intro σ' hs he
    obtain ⟨τ1, e1, s1, h1⟩ := ih σ' hs he
    exact ⟨τ1, WExec.ifsF (by rw [hs.bit]; exact hb) e1, s1, h1⟩
  | whrF hv =>
    intro σ' hs he
    exact ⟨σ', WExec.whrF (by rw [hs.val]; exact hv), hs, he⟩
  | whrT hv _ _ ih1 ih2 =>
    intro σ' hs he
    obtain ⟨τ1, e1, s1, h1⟩ := ih1 σ' hs he
    obtain ⟨τ2, e2, s2, h2⟩ := ih2 τ1 s1 h1
    exact ⟨τ2, WExec.whrT (by rw [hs.val]; exact hv) e1 e2, s2, h2⟩
  | whsF hb =>
    intro σ' hs he
    exact ⟨σ', WExec.whsF (by rw [hs.bit]; exact hb), hs, he⟩
  | whsT hb _ _ ih1 ih2 =>
    intro σ' hs he
    obtain ⟨τ1, e1, s1, h1⟩ := ih1 σ' hs he
    obtain ⟨τ2, e2, s2, h2⟩ := ih2 τ1 s1 h1
    exact ⟨τ2, WExec.whsT (by rw [hs.bit]; exact hb) e1 e2, s2, h2⟩
  | mono _ hn ih =>
    intro σ' hs he
    obtain ⟨τ1, e1, s1, h1⟩ := ih σ' hs he
    exact ⟨τ1, WExec.mono e1 hn, s1, h1⟩

end NearQuarticWires.StageTupleOuter
