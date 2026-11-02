import Proof.Quartic.StageModularCuts.CoefficientIO

set_option autoImplicit false

namespace NearQuarticWires.StageModularCuts

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Recovery.HTParts

/-- `lem:print`, paper/paper.tex: a stream pass
retains the actual source, advances its counted cursor, and appends
exactly the specified output cells while retaining all other registers. -/
structure Flow (a b : State) (consumed : ℕ) (emitted : List Bool) : Prop where
  source : b.st 3 = a.st 3
  head : b.sh 3 = a.sh 3 + consumed
  count : b.val 5 = a.val 5 + consumed
  output : b.st 14 = a.st 14 ++ emitted
  outputHead : b.sh 14 = a.sh 14 + emitted.length
  outputCount : b.val 6 = a.val 6 + emitted.length
  registers : ∀ j : Fin 16, j ≠ 5 → j ≠ 6 → b.val j = a.val j

/-- `lem:print`, paper/paper.tex: actual stream
advancement has the exact counted append semantics. -/
theorem flow_adv (a : State) (u : List Bool) (n : ℕ) :
    Flow a (adv 3 14 6 5 a u n) n u :=
  ⟨adv_st_src (by decide) _ _ _, adv_sh_src _ _ _, adv_val_SC _ _ _,
    adv_st_dst _ _ _, adv_sh_dst (by decide) _ _ _, adv_val_OP (by decide) _ _ _,
    fun j h5 h6 => adv_val_other _ _ _ j h6 h5⟩

/-- `lem:print`, paper/paper.tex: consecutive stream
passes compose by literal byte concatenation and cursor addition. -/
theorem Flow.trans {a b c : State} {n m : ℕ} {u v : List Bool}
    (h : Flow a b n u) (h' : Flow b c m v) : Flow a c (n + m) (u ++ v) := by
  constructor
  · exact h'.source.trans h.source
  · rw [h'.head, h.head]; omega
  · rw [h'.count, h.count]; omega
  · rw [h'.output, h.output, List.append_assoc]
  · rw [h'.outputHead, h.outputHead, List.length_append]; omega
  · rw [h'.outputCount, h.outputCount, List.length_append]; omega
  · intro j h5 h6
    exact (h'.registers j h5 h6).trans (h.registers j h5 h6)

/-- `lem:print`, paper/paper.tex: output appends
preserve every binary arithmetic workspace tape. -/
theorem Workspace.append {a : State} {p q : ℕ} (h : Workspace a p q) (u : List Bool) :
    Workspace (appendO a 14 6 u) p q := by
  apply h.transport
  refine ⟨?_, ?_, rfl⟩
  · intro j hj
    have h14 : j ≠ 14 := by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj; exact hj.2
    simp [appendO, Function.update_of_ne h14]
  · intro j hj
    have h6 : j ≠ 6 := by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj; exact hj.2.1
    simp [appendO, Function.update_of_ne h6]

/-- `lem:print`, paper/paper.tex: source/output
advancement leaves the fixed binary workspace reusable. -/
theorem Workspace.advance {a : State} {p q : ℕ} (h : Workspace a p q) (u : List Bool) (n : ℕ) :
    Workspace (adv 3 14 6 5 a u n) p q := by
  apply h.transport
  refine ⟨?_, ?_, rfl⟩
  · intro j hj
    have h3 : j ≠ 3 := by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj; exact hj.1
    have h14 : j ≠ 14 := by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj; exact hj.2
    exact ⟨adv_st_other _ _ _ j h14, adv_sh_other _ _ _ j h14 h3⟩
  · intro j hj
    have h5 : j ≠ 5 := by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj; exact hj.1
    have h6 : j ≠ 6 := by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj; exact hj.2.1
    exact adv_val_other _ _ _ j h6 h5

/-- `lem:print`, paper/paper.tex: a coefficient
transfer leaves its binary workspace ready for the next row. -/
theorem transferFinal_workspace {a : State} {p q : ℕ} (h : Workspace a p q)
    (z : ℤ) (position : ℕ) : Workspace (transferFinal a p z q position) p q :=
  ((h.read z position).reduced z).append _

/-- `lem:print`, paper/paper.tex: coefficient
transfer consumes one actual signed frame and emits exactly the marked
canonical-residue frame, preserving the other runtime parameters. -/
theorem transferFinal_flow {a : State} {p q : ℕ} (h : Workspace a p q)
    (z : ℤ) (hs : a.sh 3 = a.val 5) :
    Flow a (transferFinal a p z q (a.val 5 + (2 * p + 3))) (2 * p + 3)
      (marks (frame (MatrixScoreBatch.signMagnitude p (z % (q : ℤ))))) := by
  let b := atRec 3 coefficient 5 a (MatrixScoreBatch.signMagnitude p z) (a.val 5 + (2 * p + 3))
  have hb := h.read z (a.val 5 + (2 * p + 3))
  have hf := coefficientFinal_frame b p z q hb.sign
  have hv := coefficientFinal_registers b p z q hb.sign
  have hh := coefficientFinal_heads b p z q
  constructor
  · change (appendO (coefficientFinal b p z q) 14 6 _).st 3 = a.st 3
    simp only [appendO_st]
    rw [Function.update_of_ne (show (3 : Fin 16) ≠ 14 by decide), hf.st (by decide)]
    simp [b, atRec, coefficient]
  · change (appendO (coefficientFinal b p z q) 14 6 _).sh 3 = _
    simp only [appendO_sh]
    rw [Function.update_of_ne (show (3 : Fin 16) ≠ 14 by decide), hh]
    simp [b, atRec, hs]
  · change (appendO (coefficientFinal b p z q) 14 6 _).val 5 = _
    simp only [appendO_val]
    rw [Function.update_of_ne (show (5 : Fin 16) ≠ 6 by decide), hv]
    simp [b, atRec]
  · change (appendO (coefficientFinal b p z q) 14 6 _).st 14 = _
    simp only [appendO_st, Function.update_self]
    rw [hf.st (by decide)]
    simp [b, atRec, coefficient]
  · change (appendO (coefficientFinal b p z q) 14 6 _).sh 14 = _
    simp only [appendO_sh, Function.update_self]
    rw [hh]
    simp [b, atRec]
  · change (appendO (coefficientFinal b p z q) 14 6 _).val 6 = _
    simp only [appendO_val, Function.update_self]
    rw [hv]
    simp [b, atRec]
  · intro j h5 h6
    change (appendO (coefficientFinal b p z q) 14 6 _).val j = _
    simp only [appendO_val]
    rw [Function.update_of_ne h6, hv]
    simp [b, atRec, Function.update_of_ne h5]

end NearQuarticWires.StageModularCuts
