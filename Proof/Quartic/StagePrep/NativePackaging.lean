import Proof.Quartic.StagePrep.CanonicalProgram
import Proof.Gates.Dispatch.Run
import Proof.Gates.Dispatch.Main

/-!
# The physical preparation program and its original-call clock

Paper: the encoded calls of `thm:counter`, paper/paper.tex, and the bounded witness read and preparation
cost of `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open NearCubicGates.Close.Interfaces
open NearCubicGates.Close.WordPrograms
open NearCubicWires.RepairOrdinary

/-- The physical preparation budget of `prop:time`,
paper/paper.tex, includes output framing,
fixed-word compilation, call-only setup and rewinding only
the actually visited witness prefix. -/
def nativePreparationBudget (K : ℕ) (N : ℕ → ℕ) (c : Call) (_w : List Bool) : ℕ :=
  budgetOf VV K (callWord c).length (3*N (callWord c).length+2)

/-- A concrete raw preparation execution for `prop:time`,
paper/paper.tex, becomes a cold physical run
at the same original-call clock. The setup scans only the call
frame, and its budget does not depend on witness length. -/
theorem nativePreparation_run (B1 B2 K : ℕ) (hK : 1≤K) (c : Call) (w : List Bool)
    (b : DS VV) (n N : ℕ)
    (hex : Ex (ctxOf K (callWord c) w) (rawPreparationProgram B1 B2) a0 b n)
    (hout : b.out=Program.prepWord B1 B2 c w) (hn : n≤N) :
    ∃ τ, WXExec (capOf K (callWord c) w (3*N+2))
      (prog K (framedPreparationProgram B1 B2))
      (startState (VV+3) NR (Program.requestWord (c,w))) τ
      (budgetOf VV K (callWord c).length (3*N+2)) ∧
      τ.st sOUT=frame (Program.prepWord B1 B2 c w) ∧
      (∀ i,τ.sh i=0) ∧ ∀ q,τ.val q=0 := by
  have hf := framedProgram_spec hex
  have hf' : Ex (ctxOf K (callWord c) w) (framedPreparationProgram B1 B2)
      a0 (framedState b) (3*n+2) := by
    simpa only [framedPreparationProgram,markedState,a0,markedBits,List.flatMap_nil] using hf
  obtain ⟨τ,hrun,hout',hsh,hval⟩ :=
    prog_spec K hK (framedPreparationProgram B1 B2) (callWord c) w hf' (3*N+2) (by omega)
  refine ⟨τ,hrun,?_,hsh,hval⟩
  rw [hout']
  change frame b.out=frame (Program.prepWord B1 B2 c w)
  rw [hout]

/-- The physical compiler for the preparation instructions of
`prop:time`, paper/paper.tex. Its premise is
the proved execution of the concrete raw program on every
call, rather than a replacement machine or budget assumption. -/
noncomputable def preparationWordFunction_of_raw_execution
    (B1 B2 K : ℕ) (hK : 1≤K) (N : ℕ → ℕ)
    (hmain : ∀ (c : Call) (w : List Bool), ∃ b n,
      Ex (ctxOf K (callWord c) w) (rawPreparationProgram B1 B2) a0 b n ∧
        b.out=Program.prepWord B1 B2 c w ∧ n≤N (callWord c).length) :
    WordFunction (Call×List Bool) Program.requestWord
      (fun r => frame (Program.prepWord B1 B2 r.1 r.2))
      (fun r => nativePreparationBudget K N r.1 r.2) :=
  wordFunction_of_wmx (prog K (framedPreparationProgram B1 B2)) sOUT (by simp)
    (fun r => capOf K (callWord r.1) r.2 (3*N (callWord r.1).length+2))
    (by
      intro r
      obtain ⟨b,n,hex,hout,hn⟩ := hmain r.1 r.2
      exact nativePreparation_run B1 B2 K hK r.1 r.2 b n _ hex hout hn)

/-- Polynomial work for the source preparation instructions
of `prop:time`, paper/paper.tex, remains
polynomial after the actual call-only setup, framing, fixed-word
compilation and bounded-prefix rewind. -/
theorem nativePreparationBudget_poly (K : ℕ) (N : ℕ → ℕ) (hN : PolyB N) :
    Program.PolyCost (nativePreparationBudget K N) := by
  have hp : PolyB (fun L => budgetOf VV K L (3*N L+2)) := by
    unfold budgetOf setupCost KC wdOf
    repeat (first | exact hN | with_reducible exact PolyB.const _ |
      with_reducible exact PolyB.id | with_reducible apply PolyB.add |
      with_reducible apply PolyB.mul | with_reducible apply PolyB.pow)
  obtain ⟨C,e,hCe⟩ := hp
  exact ⟨C,e,fun c _ => hCe (callWord c).length⟩

end NearQuarticWires.StagePrep
