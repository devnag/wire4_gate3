import Proof.Quartic.StageModularCuts.KernelFrame
import Proof.Gates.CounterAsm.Copy

set_option autoImplicit false

namespace NearQuarticWires.StageModularCuts

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicGates.Close.WordPrograms

/-- `lem:print`, paper/paper.tex: the reusable
binary workspace has fixed-width words and zero arithmetic counters. -/
structure Workspace (a : State) (p q : ℕ) : Prop where
  words : ∃ x u v t, Words a (p + 1) x q u v t
  clear : Clear a
  sign : a.val sign = 0
  head : a.sh coefficient = 0
  length : (a.st coefficient).length ≤ 2 * (p + 1) + 1

/-- `lem:print`, paper/paper.tex: source and output
cursor operations preserve the coefficient workspace. -/
theorem Workspace.transport {a b : State} {p q : ℕ} (h : Workspace a p q)
    (hf : SameExcept a b [3, 14] [5, 6, 9, 10, 12]) : Workspace b p q := by
  obtain ⟨x, u, v, t, hw⟩ := h.words
  refine ⟨⟨x, u, v, t, ?_⟩, ?_, ?_, ?_, ?_⟩
  · exact ⟨hf.numOn (by decide) hw.input, hf.numOn (by decide) hw.divisor,
      hf.numOn (by decide) hw.quotient, hf.numOn (by decide) hw.remainder,
      hf.numOn (by decide) hw.temporary⟩
  · exact ⟨(hf.val (by decide)).trans h.clear.flag,
      (hf.val (by decide)).trans h.clear.rewind,
      (hf.val (by decide)).trans h.clear.rounds,
      (hf.val (by decide)).trans h.clear.counter⟩
  · exact (hf.val (by decide)).trans h.sign
  · exact (hf.sh (by decide)).trans h.head
  · rw [hf.st (show coefficient ∉ [(3 : Fin 16), 14] by decide)]
    exact h.length

/-- `lem:print`, paper/paper.tex: one coefficient
reduction preserves the workspace for all following rows. -/
theorem Workspace.reduced {a : State} {p q : ℕ} (h : Workspace a p q) (z : ℤ) :
    Workspace (coefficientFinal a p z q) p q := by
  obtain ⟨x, u, v, t, hw⟩ := h.words
  obtain ⟨x', u', hw'⟩ := coefficientFinal_words a p z q x u v t hw
  refine ⟨⟨x', u', _, 0, hw'⟩, ?_, ?_, ?_, ?_⟩
  · have he := coefficientFinal_registers a p z q h.sign
    exact ⟨by rw [he]; exact h.clear.flag, by rw [he]; exact h.clear.rewind,
      by rw [he]; exact h.clear.rounds, by rw [he]; exact h.clear.counter⟩
  · rw [coefficientFinal_registers a p z q h.sign]
    exact h.sign
  · rw [coefficientFinal_heads]
    exact h.head
  · rw [coefficientFinal_word, frame_length, MatrixScoreBatch.signMagnitude_length]

/-- `lem:print`, paper/paper.tex: reading an actual
signed field sets the coefficient word and advances only the source
cursor, preserving all arithmetic workspace words. -/
theorem Workspace.read {a : State} {p q : ℕ} (h : Workspace a p q)
    (z : ℤ) (position : ℕ) :
    Workspace (atRec 3 coefficient 5 a (MatrixScoreBatch.signMagnitude p z) position) p q := by
  obtain ⟨x, u, v, t, hw⟩ := h.words
  have hn {j : Fin 16} {v : ℕ} (hj : j ≠ coefficient) (hj3 : j ≠ 3)
      (hv : NumOn a j (p + 1) v) :
      NumOn (atRec 3 coefficient 5 a (MatrixScoreBatch.signMagnitude p z) position) j (p + 1) v := by
    constructor
    · simpa [atRec, Function.update_of_ne hj] using hv.1
    · simpa [atRec, Function.update_of_ne hj3] using hv.2
  refine ⟨⟨x, u, v, t, ⟨hn (by decide) (by decide) hw.input,
    hn (by decide) (by decide) hw.divisor, hn (by decide) (by decide) hw.quotient,
    hn (by decide) (by decide) hw.remainder, hn (by decide) (by decide) hw.temporary⟩⟩,
    ?_, ?_, ?_, ?_⟩
  · constructor
    · simpa [atRec, flag] using h.clear.flag
    · simpa [atRec, rewind] using h.clear.rewind
    · simpa [atRec, rounds] using h.clear.rounds
    · simpa [atRec, counter] using h.clear.counter
  · simpa [atRec, StageModularCuts.sign] using h.sign
  · simpa [atRec, coefficient] using h.head
  · simp [atRec, frame_length, MatrixScoreBatch.signMagnitude_length]

end NearQuarticWires.StageModularCuts
