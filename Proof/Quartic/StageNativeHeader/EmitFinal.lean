import Proof.Quartic.StageNativeHeader.EmitCore

/-!
# The emission of the native table request: the delivered statements

Paper: `lem:print`, paper/paper.tex, and `prop:time`.

`emitP_exec`: from `EmitReady r`, for every capacity of at least `emitCap r`, the emission leaves
`marks (table.word)` on the accumulator, head at `0`, within `emitCost r` steps, the registers of the final copy at
`0`. `emitP_avoids`: no instruction of the emission touches the output stream.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearQuarticWires.StageNativeHeader

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.RepairRepresentation (natWord)
open NearQuarticWires.StagePrint NearQuarticWires.StagePrint.Downstream
open NearQuarticWires.Control

/-! ## The output stream is never touched -/

/-- Whether an instruction of the program moves or writes the stream `i`. -/
def emitTouches {ns nr : ℕ} (i : Fin (ns + 1)) : WM ns nr → Bool
  | .skip => false
  | .inc _ => false
  | .dec _ => false
  | .fwd j => decide (j = i)
  | .bwd j => decide (j = i)
  | .wr j _ => decide (j = i)
  | .setc _ => false
  | .seq P Q => emitTouches i P || emitTouches i Q
  | .ifr _ P Q => emitTouches i P || emitTouches i Q
  | .ifs _ P Q => emitTouches i P || emitTouches i Q
  | .whr _ P => emitTouches i P
  | .whs _ P => emitTouches i P

theorem avoids_of_emitTouches {ns nr : ℕ} (i : Fin (ns + 1)) :
    ∀ P : WM ns nr, emitTouches i P = false → WM.Avoids i P
  | .skip, _ => trivial
  | .inc _, _ => trivial
  | .dec _, _ => trivial
  | .fwd j, h => by simpa [emitTouches, WM.Avoids] using h
  | .bwd j, h => by simpa [emitTouches, WM.Avoids] using h
  | .wr j _, h => by simpa [emitTouches, WM.Avoids] using h
  | .setc _, _ => trivial
  | .seq P Q, h => by
    simp only [emitTouches, Bool.or_eq_false_iff] at h
    exact ⟨avoids_of_emitTouches i P h.1, avoids_of_emitTouches i Q h.2⟩
  | .ifr _ P Q, h => by
    simp only [emitTouches, Bool.or_eq_false_iff] at h
    exact ⟨avoids_of_emitTouches i P h.1, avoids_of_emitTouches i Q h.2⟩
  | .ifs _ P Q, h => by
    simp only [emitTouches, Bool.or_eq_false_iff] at h
    exact ⟨avoids_of_emitTouches i P h.1, avoids_of_emitTouches i Q h.2⟩
  | .whr _ P, h => avoids_of_emitTouches i P h
  | .whs _ P, h => avoids_of_emitTouches i P h

/-- **The emission avoids the output stream.** -/
theorem emitP_avoids : WM.Avoids sOUT emitP := avoids_of_emitTouches _ _ (by decide)

/-! ## The cost -/

theorem numCost_le (v X : ℕ) (hX : 2 ≤ X) (hb : natBitLength v ≤ X) (hv : v ≤ X) : numCost v ≤ 2000 * X ^ 2 := by
  unfold numCost
  have h1 : (natBitLength v + 10) * (100 * v + 200) ≤ (X + 10) * (100 * X + 200) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h2 : (X + 10) * (100 * X + 200) = 100 * X ^ 2 + 1200 * X + 2000 := by ring
  have h3 : 2 * X ≤ X ^ 2 := by nlinarith
  omega

theorem numCostG_le (v X Y : ℕ) (hX : 2 ≤ X) (hY : 1 ≤ Y) (hb : natBitLength v ≤ X) (hv : v ≤ Y) :
    numCost v ≤ 3000 * (X * Y) := by
  unfold numCost
  have h1 : (natBitLength v + 10) * (100 * v + 200) ≤ (X + 10) * (100 * Y + 200) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h2 : (X + 10) * (100 * Y + 200) = 100 * (X * Y) + 200 * X + 1000 * Y + 2000 := by ring
  have h3 : X ≤ X * Y := Nat.le_mul_of_pos_right X hY
  have h4 : 2 * Y ≤ X * Y := Nat.mul_le_mul_right _ hX
  omega

/-- **The cost of the emission** is within `emitCost`. -/
theorem coreCost_le (n p d G nC ns U q : ℕ) (hd : d ≤ n) (hGU : G ≤ U) (hU1 : 1 ≤ U) (hUd : 2 ^ d = U)
    (hC : nC ≤ 3 * (n + 2) ^ 2) (hq : q = d + 2 * p + 3) (hG2 : natBitLength G ≤ n + 1) :
    coreCost d p G nC ns U q ≤ 10 ^ 12 * (n + p + 2) ^ 4 * (ns + U * U + 1) := by
  obtain ⟨X, hX⟩ : ∃ X, X = n + p + 2 := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y, Y = ns + U * U + 1 := ⟨_, rfl⟩
  rw [← hX, ← hY]
  have hX2 : 2 ≤ X := by omega
  have hY1 : 1 ≤ Y := by omega
  have hUU : U ≤ U * U := Nat.le_mul_of_pos_left U hU1
  have hUY : U * U ≤ Y := by omega
  have hnd := emit_nbl_le d
  have hnp := emit_nbl_le p
  have c1 := numCost_le d X hX2 (by omega) (by omega)
  have c2 := numCost_le p X hX2 (by omega) (by omega)
  have c3 := numCostG_le G X Y hX2 hY1 (by omega) (by omega)
  have hXX : X ≤ X ^ 2 := by nlinarith
  have hX2Y : X ^ 2 ≤ X ^ 2 * Y := Nat.le_mul_of_pos_right _ hY1
  have hXY : X * Y ≤ X ^ 2 * Y := Nat.mul_le_mul_right _ hXX
  have hYZ : Y ≤ X ^ 2 * Y := Nat.le_mul_of_pos_left Y (by positivity)
  have hX4 : X ^ 2 * Y ≤ X ^ 4 * Y :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (by norm_num))
  have hC' : nC ≤ 3 * X ^ 2 := hC.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
  have hu : d * (18 * 2 ^ d + 7) ≤ 18 * (X * Y) + 7 * X := by
    have : d * (18 * 2 ^ d + 7) ≤ X * (18 * Y + 7) := by
      rw [hUd]; exact Nat.mul_le_mul (by omega) (by omega)
    have e : X * (18 * Y + 7) = 18 * (X * Y) + 7 * X := by ring
    omega
  have hs : U * (54 * U + 9) ≤ 63 * Y := by
    have e : U * (54 * U + 9) = 54 * (U * U) + 9 * U := by ring
    omega
  have hO : outLen (2 * natBitLength d + 1) (2 * natBitLength p + 1) (2 * natBitLength G + 1) nC ns U q ≤
      300 * (X ^ 2 * Y) := by
    unfold outLen; omega
  calc coreCost d p G nC ns U q ≤ 20000 * (X ^ 4 * Y) := by unfold coreCost; omega
    _ ≤ 10 ^ 12 * (X ^ 4 * Y) := Nat.mul_le_mul_right _ (by norm_num)
    _ = 10 ^ 12 * X ^ 4 * Y := by ring

theorem nblG_le (r : NativeHeaderRequest) :
    natBitLength r.table.matrix.cuts.length ≤ r.parameters.n + 1 := by
  have h1 := Nat.log_mono_right (b := 2) (emit_cuts_le_U r)
  rw [emit_U_eq, Nat.log_pow (by norm_num)] at h1
  have h2 := emit_dRow_le r.parameters
  unfold natBitLength
  omega

theorem zeroRegs_free : ∀ x ∈ (zeroRegs : List (Fin hnr)), x ∉ keptRegs := by decide

/-- **The emission of the native table request** (`lem:print`, paper/paper.tex): from
`EmitReady r`, for every capacity of at least `emitCap r`, the accumulator ends holding `marks (table.word)`, head
at `0`, within `emitCost r` steps, the registers of the final copy at `0`. -/
theorem emitP_exec (r : NativeHeaderRequest) (cap : ℕ) (hcap : emitCap r ≤ cap) (σ : WState hns hnr)
    (h : EmitReady r σ) :
    ∃ τ, WExec cap emitP σ τ (emitCost r) ∧ τ.st sACC = Streaming.marks r.table.word ∧ τ.sh sACC = 0 ∧
      τ.val rFO = 0 ∧ τ.val rFC = 0 := by
  have hy : σ.st sY = marks (colsContent r.parameters) ++ [false] := by
    rw [h.cols, NearCubicGates.Close.Codec.frame_eq_marks]
  have hlen := pieces_length (PrimT.C4Geo.dRow r.parameters) r.table.matrix.p r.table.matrix.cuts.length
    r.table.matrix.U r.table.q (colsContent r.parameters) r.stream
  have hpc : pieces (PrimT.C4Geo.dRow r.parameters) r.table.matrix.p r.table.matrix.cuts.length r.table.matrix.U
      r.table.q (colsContent r.parameters) r.stream = marks r.table.word := (marks_table_word r).symm
  have hfr : (frame r.table.word).length = (marks r.table.word).length + 1 := by
    rw [NearCubicGates.Close.Codec.frame_eq_marks, List.length_append, List.length_singleton]
  have hq4 : 4 * r.table.q ≤ outLen (natWord (PrimT.C4Geo.dRow r.parameters)).length
      (natWord r.table.matrix.p).length (natWord r.table.matrix.cuts.length).length
      (colsContent r.parameters).length r.stream.length r.table.matrix.U r.table.q := by
    unfold outLen; omega
  have hcnt := emit_count_eq r
  obtain ⟨τ, e, hacc, hah, hv⟩ := emitCore_exec cap σ (PrimT.C4Geo.dRow r.parameters) r.table.matrix.p
    r.table.matrix.cuts.length r.table.matrix.U r.table.q (colsContent r.parameters) r.stream (fieldsWord r)
    h.inp h.inph hy h.colsh h.acc h.acch h.zd h.zdh h.zp h.zph h.zg h.zgh h.vD h.vP h.vG
    (fun x hx => h.zero x (zeroRegs_free x hx)) (emit_U_eq r) (emit_q_eq r) (emit_cuts_le_U r)
    (by unfold emitCap at hcap; rw [← hlen, hpc] at hq4 ⊢; omega)
  have hcost : coreCost (PrimT.C4Geo.dRow r.parameters) r.table.matrix.p r.table.matrix.cuts.length
      (colsContent r.parameters).length r.stream.length r.table.matrix.U r.table.q ≤ emitCost r :=
    coreCost_le r.parameters.n _ _ _ _ _ _ _ (emit_dRow_le _) (emit_cuts_le_U r) (emit_U_pos r) (emit_U_eq r).symm
      (emit_colsContent_length_le _) (emit_q_eq r) (nblG_le r)
  refine ⟨τ, WExec.mono e hcost, by rw [hacc, hpc], hah, ?_, ?_⟩
  · rw [hv rFO (by decide)]; exact h.zero rFO (by decide)
  · rw [hv rFC (by decide)]; exact h.zero rFC (by decide)

end NearQuarticWires.StageNativeHeader
