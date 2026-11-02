import Proof.Quartic.Reconstruct.EmitStage

/-!
# The run of the emission stage

Paper: Step 3 of `sec:algorithm`, paper/paper.tex.

Run from the initial state on `gatheredWord q` with a width of at least `emitWidth q`, `emitS` prints
`frame (systemsWord q)` within `emitRunCost q W` steps (`emitS_run`).
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces (listWord bitWord)
open NearQuarticWires.Greedy NearQuarticWires.Program

variable {B1 B2 : ℕ}

/-- The cost of the emission stage for a child at width `W`. -/
noncomputable def emitRunCost (q : ChildRequest B1 B2) (W : ℕ) : ℕ :=
  5 + headCost (W - 2) q.cellCall.J q.cellCall.ncol + ((systemList q).length * (itemCostQ q W + 4) + 4) + 3 + 3

/-- **The emission stage prints the framed systems.** -/
theorem emitS_run (q : ChildRequest B1 B2) (C : Ctx) (hinp : C.inp = gatheredWord q) (hW : emitWidth q ≤ C.Wd) :
    Hs C emitS (a0 : DS VV MM) (emitRunCost q C.Wd) (fun b => b.out = RepairOrdinary.frame (systemsWord q)) := by
  have hEW := emitExp_le q
  have hW2 : 2 * emitExp q + 2 ≤ C.Wd := hEW.trans hW
  refine Hx.hs (Hs.then (NearCubicGates.Close.CounterMachine.PrefixProg.cstInit_spec C (by omega))
    (fun d ⟨cd, dram, drc, dip, dout, _, _, _⟩ n0 hn0 => ?_))
  have hin : C.inp.drop d.ip = headWord q.call.n q.selected.1.M1 q.selected.1.A q.selected.1.Lambda q.cellCall.J
      (if decide (q.call.kind = .pair) then 1 else 0) (2 * Algorithm.traceOrder * Builder.occurrences q.call 0)
      (2 * Algorithm.traceOrder * Builder.occurrences q.call 1) q.cellCall.ncol (tablesPerGroup q)
      (systemList q).length q.selected.1.factors (certNats q) ++
      ((systemList q).flatMap (gatheredItem q) ++ []) := by
    rw [dip, List.drop_zero, hinp, gatheredWord_eq, List.append_nil]
  have hZ : ∀ s : Fin MM, d.ram s = [] ∧ d.rc s = 0 := fun s => by rw [dram, drc]; exact ⟨rfl, rfl⟩
  refine Hs.then (headS_spec d cd q.call.n q.selected.1.M1 q.selected.1.A q.selected.1.Lambda q.cellCall.J
    (if decide (q.call.kind = .pair) then 1 else 0) (2 * Algorithm.traceOrder * Builder.occurrences q.call 0)
    (2 * Algorithm.traceOrder * Builder.occurrences q.call 1) q.cellCall.ncol (tablesPerGroup q)
    (systemList q).length q.selected.1.factors (certNats q) _ hin (hZ sF) (hZ sZ) (C.Wd - 2)
    (fun v hv => (natBitLength_le_of_lt_two_pow (head_values_lt q v hv) (by unfold emitExp; omega)).trans
      (by omega)) (by omega))
    (fun b1 ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, c1⟩ n1 hn1 => ?_)
  have ctx : CtxHeld q b1 := ⟨h1, h2, h3, h6, h7, h4, h5, h9, by rw [h10, factors_length],
    by rw [(h13 sDp (by decide) (by decide)).2, (hZ sDp).2]; omega,
    by rw [(h13 sDn (by decide) (by decide)).2, (hZ sDn).2]; omega⟩
  have hin1 : C.inp.drop b1.ip = (systemList q).flatMap (gatheredItem q) ++ [] := by
    rw [h11]; exact drop_step hin
  have hmW : (systemList q).length < 2 ^ C.Wd :=
    lt_of_lt_of_le (systemList_length_lt q) (Nat.pow_le_pow_right (by norm_num) (by omega))
  refine Hs.then (itemsLoopS_spec q b1 c1 [] hin1 ctx h8 hmW hW) (fun b2 ⟨m2, _, c2⟩ n2 hn2 => ?_)
  refine Hs.last (putD_spec 0 false b2) (fun b3 w3 n3 hn3 => ⟨?_, ?_⟩)
  · rw [w3.out, m2.out, h12, dout, frame_systemsWord]
    simp only [List.nil_append, List.append_assoc]
  · rw [factors_length, certNats_length] at hn1
    have : 2 * 2 ^ 0 + 1 = 3 := by norm_num
    rw [this] at hn3
    unfold emitRunCost
    omega

end NearQuarticWires.Reconstruct
