import Proof.Quartic.StageNativeHeader.Ready

/-!
# From the input to the state after the column call

Paper: `lem:print`, paper/paper.tex.

`preP` reads the five fields and writes the input of the column printer (`pre_exec`, from the initial state on the
input word). After the column call, the ideal state `calledIdeal` satisfies `PostPre` (`postPre_called`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageNativeHeader

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.Streaming (marks marks_append)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat (appendO appendO_st appendO_sh appendO_val appendO_cell)
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicGates.Close.Expand.PolyTab (idealStart)
open NearQuarticWires.Control NearQuarticWires.StagePrint NearQuarticWires.StagePrint.Downstream

variable (cap : ℕ)

/-- The initial state on the input word. -/
noncomputable def start (r : NativeHeaderRequest) : WState hns hnr := idealStart hns hnr r.word (fun _ => 0)

theorem start_st (r : NativeHeaderRequest) (i : Fin (hns + 1)) :
    (start r).st i = if i.val = 0 then frame r.word else [] := by
  simp [start, idealStart]

theorem frame_word (r : NativeHeaderRequest) : frame r.word = marks (fieldsWord r) ++ (marks r.stream ++ [false]) := by
  rw [NearCubicGates.Close.Codec.frame_eq_marks, word_eq, marks_append, List.append_assoc]

/-- Read the fields and write the input of the column printer. -/
noncomputable def preP : WM hns hnr := .seq parseP bankP

/-- The cost of `preP`. -/
def preCost (r : NativeHeaderRequest) : ℕ := parseCost r + 1 + bankCost r.parameters

/-- The capacity used by `preP`. -/
def preCap (r : NativeHeaderRequest) : ℕ :=
  8 * (StageColumns.columnInput r.parameters).length + 4 * (r.parameters.n + r.parameters.r + r.parameters.b +
    r.parameters.s + r.table.matrix.p) + 104

/-- The state after `preP`. -/
structure PreDone (r : NativeHeaderRequest) (σ : WState hns hnr) : Prop where
  inp : σ.st sIN = frame r.word
  inph : σ.sh sIN = (marks (fieldsWord r)).length
  bank : σ.st sB0 = frame (StageColumns.columnInput r.parameters)
  bankh : σ.sh sB0 = 0
  other : ∀ i, i ≠ sIN → i ≠ sB0 → σ.st i = [] ∧ σ.sh i = 0
  vN : σ.val rN = r.parameters.n
  vR : σ.val rR = r.parameters.r
  vB : σ.val rB = r.parameters.b
  vS : σ.val rS = r.parameters.s
  vP : σ.val rP = r.table.matrix.p
  zero : ∀ x, x ∉ [rN, rR, rB, rS, rP] → σ.val x = 0

theorem pow_nbl_succ_le (x : ℕ) : 2 ^ (natBitLength x + 1) ≤ 4 * (x + 1) := by
  have := NearCubicGates.Close.CounterMachine.PrefixProg.pow_nbl_le x
  rw [pow_succ]; omega

theorem sB0_ne_IN : sB0 ≠ sIN := sne (by simp [sB0, sbank, sIN, strm])

/-- **The fields and the input of the column printer.** -/
theorem pre_exec (r : NativeHeaderRequest) (hcap : preCap r ≤ cap) :
    ∃ σ, WExec cap preP (start r) σ (preCost r) ∧ PreDone r σ := by
  have s0 : ∀ i, (start r).sh i = 0 := fun i => rfl
  have v0 : ∀ x, (start r).val x = 0 := fun x => rfl
  obtain ⟨τ1, e1, f1, s1, h1, n1, r1, b1, ss1, p1⟩ := parse_exec cap r (start r) (marks r.stream ++ [false])
    (by rw [start_st, if_pos (by simp [sIN, strm]), frame_word]) (s0 sIN) (fun y _ => v0 y)
    (fun x hx => by
      have := pow_nbl_succ_le x
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      unfold preCap at hcap
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> omega)
  have hB : τ1.st sB0 = [] := by
    rw [f1.st sB0 (by simp [sB0_ne_IN]), start_st, if_neg (by simp [sB0, sbank])]
  obtain ⟨τ2, e2, f2, b2, bh2⟩ := bank_exec cap r.parameters τ1 hB (by rw [f1.sh sB0 (by simp [sB0_ne_IN])]; rfl)
    n1 r1 b1 ss1 (fun y hy => by rw [f1.val y (by revert hy; revert y; decide)]; rfl) (by unfold preCap at hcap; omega)
  refine ⟨τ2, WExec.mono (WExec.seq e1 e2) le_rfl, ?_⟩
  exact {
    inp := by rw [f2.st sIN (by simp [Ne.symm sB0_ne_IN]), s1, start_st, if_pos (by simp [sIN, strm])]
    inph := by rw [f2.sh sIN (by simp [Ne.symm sB0_ne_IN]), h1]
    bank := b2
    bankh := bh2
    other := fun i h1' h2' => by
      rw [f2.st i (by simp [h2']), f2.sh i (by simp [h2']), f1.st i (by simp [h1']), f1.sh i (by simp [h1']),
        start_st, if_neg (fun h => h1' (Fin.ext (by simpa [sIN, strm] using h)))]
      exact ⟨rfl, rfl⟩
    vN := by rw [f2.val rN (by simp), n1]
    vR := by rw [f2.val rR (by simp), r1]
    vB := by rw [f2.val rB (by simp), b1]
    vS := by rw [f2.val rS (by simp), ss1]
    vP := by rw [f2.val rP (by simp), p1]
    zero := fun x hx => by rw [f2.val x (by simp), f1.val x hx]; rfl }

/-! ## After the column call -/

theorem calledIdeal_sCD (σ : WState hns hnr) (tapes : Fin tc → List Bool) (steps : ℕ) (P : StarParams) :
    (calledIdeal σ tapes steps P).st sCD = σ.st sCD ∧ (calledIdeal σ tapes steps P).sh sCD = σ.sh sCD := by
  have hb : ∀ j, site.bank j ≠ sCD := fun j h => by
    have := congrArg Fin.val h; simp [site, sbank, sCD, strm] at this; omega
  have hT : sCD ≠ site.tally := sne (by simp [site, sTA, sCD, strm])
  have hG : sCD ≠ site.guard := sne (by simp [site, sGA, sCD, strm])
  have hY : sCD ≠ sY := sne (by simp [sY, sCD, strm])
  constructor
  · simp only [calledIdeal, cleanState, calledState, WState.sets_st, Function.update_of_ne hG,
      Function.update_of_ne hT]
    rw [NearCubicGates.Close.WordPrograms.updS_st_other site.bank _ _ _ sCD hb]
    simp only [appendO_st, Function.update_of_ne hY, WState.sets_st, Function.update_of_ne hG,
      Function.update_of_ne hT]
    exact NearCubicGates.Close.WordPrograms.updS_st_other site.bank _ _ _ sCD hb
  · simp only [calledIdeal, cleanState, calledState, WState.sets_sh]
    rw [NearCubicGates.Close.WordPrograms.updS_sh_other site.bank _ _ _ sCD hb]
    simp only [appendO_sh, Function.update_of_ne hY, WState.sets_sh]
    exact NearCubicGates.Close.WordPrograms.updS_sh_other site.bank _ _ _ sCD hb

/-- **The ideal state after the column call.** -/
theorem postPre_called (r : NativeHeaderRequest) (σ : WState hns hnr) (h : PreDone r σ) (tapes : Fin tc → List Bool)
    (steps : ℕ) : PostPre r (calledIdeal σ tapes steps r.parameters) := by
  have hYne : sY ≠ sIN := sne (by simp [sY, sIN, strm])
  have hY := calledIdeal_Y σ tapes steps r.parameters
  have hYe := h.other sY hYne (sne (by simp [sY, sB0, sbank, strm]))
  have hv := calledIdeal_val σ tapes steps r.parameters
  have oth : ∀ i, i.val < 10 → i ≠ sY → i ≠ sIN → i ≠ sB0 →
      (calledIdeal σ tapes steps r.parameters).st i = [] ∧ (calledIdeal σ tapes steps r.parameters).sh i = 0 :=
    fun i hi h1 h2 h3 => by
      rw [(calledIdeal_st σ tapes steps r.parameters i hi h1).1, (calledIdeal_st σ tapes steps r.parameters i hi h1).2]
      exact h.other i h2 h3
  have hIN := calledIdeal_st σ tapes steps r.parameters sIN (by simp [sIN, strm]) (Ne.symm hYne)
  exact {
    inp := by rw [hIN.1, h.inp, frame_word, List.append_assoc]
    inph := by rw [hIN.2, h.inph]
    y := by rw [hY.1, hYe.1, List.nil_append]
    yh := by rw [hY.2, hYe.2, Nat.zero_add]
    oy := by rw [hv]; simp [h.zero rOY (by decide)]
    empty := fun i hi => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact oth _ (by simp [sY2, strm]) (sne (by simp [sY, sY2, strm])) (sne (by simp [sIN, sY2, strm]))
          (sne (by simp [sB0, sbank, sY2, strm]))
      · exact oth _ (by simp [sX, strm]) (sne (by simp [sY, sX, strm])) (sne (by simp [sIN, sX, strm]))
          (sne (by simp [sB0, sbank, sX, strm]))
      · rw [(calledIdeal_sCD σ tapes steps r.parameters).1, (calledIdeal_sCD σ tapes steps r.parameters).2]
        exact h.other _ (sne (by simp [sIN, sCD, strm])) (sne (by simp [sB0, sbank, sCD, strm]))
      · exact oth _ (by simp [sACC, strm]) (sne (by simp [sY, sACC, strm])) (sne (by simp [sIN, sACC, strm]))
          (sne (by simp [sB0, sbank, sACC, strm]))
      · exact oth _ (by simp [sZd, strm]) (sne (by simp [sY, sZd, strm])) (sne (by simp [sIN, sZd, strm]))
          (sne (by simp [sB0, sbank, sZd, strm]))
      · exact oth _ (by simp [sZp, strm]) (sne (by simp [sY, sZp, strm])) (sne (by simp [sIN, sZp, strm]))
          (sne (by simp [sB0, sbank, sZp, strm]))
      · exact oth _ (by simp [sZG, strm]) (sne (by simp [sY, sZG, strm])) (sne (by simp [sIN, sZG, strm]))
          (sne (by simp [sB0, sbank, sZG, strm]))
    vN := by rw [hv, Function.update_of_ne (by decide), h.vN]
    vR := by rw [hv, Function.update_of_ne (by decide), h.vR]
    vB := by rw [hv, Function.update_of_ne (by decide), h.vB]
    vS := by rw [hv, Function.update_of_ne (by decide), h.vS]
    vP := by rw [hv, Function.update_of_ne (by decide), h.vP]
    zero := fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
      rw [hv, Function.update_of_ne hx.2.2.2.2.2]
      exact h.zero x (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨hx.1, hx.2.1,
        hx.2.2.1, hx.2.2.2.1, hx.2.2.2.2.1⟩) }

end NearQuarticWires.StageNativeHeader
