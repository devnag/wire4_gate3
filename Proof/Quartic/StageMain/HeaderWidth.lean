import Proof.Gates.Cells.Run
import Proof.Gates.Cells.Kit
import Proof.Quartic.Program.Stages

/-!
# Arithmetic workspace from the literal arity header

`prop:time`, paper/paper.tex: the main pass allocates
its arithmetic width from the original arity header. The certificate
bitmap and chosen seed do not enter this width parameter. The false-tag
branch has the fixed header size zero.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces

theorem header_ones (L : ℕ) (rest : List Bool) :
    leadOnes (List.replicate L true ++ false :: rest) = L := by
  induction L with
  | zero => simp [leadOnes]
  | succ L ih => simp only [List.replicate_succ, List.cons_append, leadOnes, ih]

theorem natHeader_width (n : ℕ) (rest : List Bool) :
    leadOnes (natWord n ++ rest) = natBitLength n := by
  rw [natWord_eq, List.append_assoc, List.cons_append, header_ones]

theorem taggedCall_header_width (c : Call) (rest : List Bool) :
    leadOnes (true :: (callWord c ++ rest)) = 1 + natBitLength c.n := by
  unfold callWord
  simp only [List.append_assoc, leadOnes, natHeader_width]
  omega

theorem dispatched_greedy_header_width {B1 B2 : ℕ} {c : Call} {p : Program.Selected c}
    (hd : Program.dispatch B1 B2 c = some p) (w suffix : List Bool) :
    leadOnes (Program.greedyWord B1 B2 c w ++ suffix) = 1 + natBitLength c.n := by
  unfold Program.greedyWord Program.stageWord
  rw [hd]
  simp only [List.cons_append, List.append_assoc]
  exact taggedCall_header_width c _

theorem nondispatched_greedy_header_width {B1 B2 : ℕ} {c : Call}
    (hd : Program.dispatch B1 B2 c = none) (w suffix : List Bool) :
    leadOnes (Program.greedyWord B1 B2 c w ++ suffix) = 0 := by
  unfold Program.greedyWord Program.stageWord
  rw [hd]
  rfl

end NearQuarticWires.StageMain
