import Proof.Quartic.StageNativeHeader.Count

/-!
# From the column field to the state before the emission

Paper: `lem:print`, paper/paper.tex.

`postP` reads the dense width (`widthP`), computes `(r/2)s`, `d` and the stride (`dimsP`), and counts the cuts
(`countP`). From the state after the column call (`PostPre`) it reaches `EmitReady` (`post_exec`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageNativeHeader

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.Streaming (marks marks_append)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearQuarticWires.Control NearQuarticWires.StagePrint NearQuarticWires.StagePrint.Downstream

variable (cap : ℕ)

/-- `(r/2)s`, `d = width − (r/2)s` and the stride. -/
noncomputable def dimsP : WM hns hnr := .seq halfMulP (.seq subP strideP)

/-- The cost of `dimsP`. -/
def dimsCost (P : StarParams) : ℕ :=
  18 * P.r + P.r / 2 * (18 * P.s + 9) + 5 + 1 + (18 * PrimT.C4Geo.width P + 23 * (P.r / 2 * P.s) + 10 + 1 +
    (36 * PrimT.C4Geo.width P + 15))

theorem dims_exec (P : StarParams) (σ : WState hns hnr) (vR : σ.val rR = P.r) (vS : σ.val rS = P.s)
    (vW : σ.val rW = PrimT.C4Geo.width P) (hz : ∀ y ∈ [rK1, rM, rD, rT2, rTmp], σ.val y = 0)
    (hcap : P.r + P.r / 2 * P.s + P.s + 2 * PrimT.C4Geo.width P + 3 ≤ cap) :
    ∃ τ, WExec cap dimsP σ τ (dimsCost P) ∧ ROnly σ τ [rK1, rM, rD, rT2] ∧ τ.val rK1 = 0 ∧
      τ.val rM = P.r / 2 * P.s ∧ τ.val rD = PrimT.C4Geo.dRow P ∧
      τ.val rT2 = 2 * PrimT.C4Geo.width P + 2 := by
  have hev : P.r % 2 = 0 := Nat.even_iff.mp P.r_even
  obtain ⟨hd, hle⟩ := dRow_eq P
  obtain ⟨τ1, e1, f1, m1, k1⟩ := halfMul_exec cap σ P.r P.s vR hev vS (hz rK1 (by simp)) (hz rM (by simp))
    (hz rTmp (by simp)) (by omega)
  obtain ⟨τ2, e2, f2, d2, k2⟩ := sub_exec cap τ1 (PrimT.C4Geo.width P) (P.r / 2 * P.s)
    (by rw [f1.val rW (by decide), vW]) m1 (by rw [f1.val rD (by decide), hz rD (by simp)]) k1
    (by rw [f1.val rTmp (by decide), hz rTmp (by simp)]) (by omega)
  have e3 := stride_exec cap τ2 (PrimT.C4Geo.width P) (by rw [f2.val rW (by decide), f1.val rW (by decide), vW])
    (by rw [f2.val rT2 (by decide), f1.val rT2 (by decide), hz rT2 (by simp)])
    (by rw [f2.val rTmp (by decide), f1.val rTmp (by decide), hz rTmp (by simp)]) (by omega)
  refine ⟨τ2.setv rT2 (2 * PrimT.C4Geo.width P + 2), WExec.mono (WExec.seq e1 (WExec.seq e2 e3)) le_rfl, ?_,
    by simp [Function.update_of_ne (show (rK1 : Fin hnr) ≠ rT2 by decide), k2], by
    simp [Function.update_of_ne (show (rM : Fin hnr) ≠ rT2 by decide), f2.val rM (by decide), m1], by
    simp [Function.update_of_ne (show (rD : Fin hnr) ≠ rT2 by decide), d2, hd], by simp⟩
  exact (f1.weaken (L' := [rK1, rM, rD, rT2]) (by simp)).trans
    ((f2.weaken (by simp)).trans (ROnly.setv τ2 (by simp) _))

/-! ## The state after the column call -/

/-- The state after the column call (ideal). -/
structure PostPre (r : NativeHeaderRequest) (σ : WState hns hnr) : Prop where
  inp : σ.st sIN = marks (fieldsWord r) ++ marks r.stream ++ [false]
  inph : σ.sh sIN = (marks (fieldsWord r)).length
  y : σ.st sY = frame (colsContent r.parameters)
  yh : σ.sh sY = (frame (colsContent r.parameters)).length
  oy : σ.val rOY = (frame (colsContent r.parameters)).length
  empty : ∀ i ∈ [sY2, sX, sCD, sACC, sZd, sZp, sZG], σ.st i = [] ∧ σ.sh i = 0
  vN : σ.val rN = r.parameters.n
  vR : σ.val rR = r.parameters.r
  vB : σ.val rB = r.parameters.b
  vS : σ.val rS = r.parameters.s
  vP : σ.val rP = r.table.matrix.p
  zero : ∀ x, x ∉ [rN, rR, rB, rS, rP, rOY] → σ.val x = 0

/-- Read the width, compute the dimensions, count the cuts. -/
noncomputable def postP : WM hns hnr := .seq widthP (.seq dimsP countP)

/-- The cost of `postP`. -/
def postCost (r : NativeHeaderRequest) : ℕ := widthCost r.parameters + 1 + (dimsCost r.parameters + 1 + countCost r)

/-- The capacity used by `postP`. -/
def postCap (r : NativeHeaderRequest) : ℕ :=
  4 * (frame (colsContent r.parameters)).length + 4 * (PrimT.C4Geo.width r.parameters + 1) + 4 * r.stream.length +
    r.table.matrix.cuts.length + r.parameters.r + r.parameters.r / 2 * r.parameters.s + r.parameters.s + 10

theorem frameReady_ne {a b : Fin (hns + 1)} (h : a.val ≠ b.val) : a ≠ b := sne h

/-- **To the state before the emission.** -/
theorem post_exec (r : NativeHeaderRequest) (σ : WState hns hnr) (h : PostPre r σ) (hcap : postCap r ≤ cap) :
    ∃ τ, WExec cap postP σ τ (postCost r) ∧ EmitReady r τ := by
  have hW2 : 2 ^ (natBitLength (PrimT.C4Geo.width r.parameters) + 1) ≤ cap := by
    have := NearCubicGates.Close.CounterMachine.PrefixProg.pow_nbl_le (PrimT.C4Geo.width r.parameters)
    unfold postCap at hcap; rw [pow_succ]; omega
  have he := h.empty
  obtain ⟨τ1, e1, f1, y1, yh1, oy1, w1⟩ := width_exec cap r.parameters σ h.y h.yh h.oy (he sY2 (by simp)).1
    (he sY2 (by simp)).2 (fun y hy => h.zero y (by revert hy; revert y; decide))
    (by unfold postCap at hcap; omega) hW2
  obtain ⟨τ2, e2, f2, k2, m2, d2, t2⟩ := dims_exec cap r.parameters τ1 (by rw [f1.val rR (by decide), h.vR])
    (by rw [f1.val rS (by decide), h.vS]) w1
    (fun y hy => by
      rw [f1.val y (by revert hy; revert y; decide)]
      exact h.zero y (by revert hy; revert y; decide))
    (by unfold postCap at hcap; omega)
  have s2 : ∀ i, τ2.st i = τ1.st i := fun i => by rw [f2.st]
  have sh2 : ∀ i, τ2.sh i = τ1.sh i := fun i => by rw [f2.sh]
  obtain ⟨τ3, e3, f3, g3⟩ := count_exec cap r τ2 (marks (fieldsWord r))
    (by rw [s2, f1.st sIN (by decide), h.inp])
    (by rw [sh2, f1.sh sIN (by decide), h.inph])
    (by rw [s2, f1.st sX (by decide)]; exact (he sX (by simp)).1)
    (by rw [sh2, f1.sh sX (by decide)]; exact (he sX (by simp)).2)
    (by rw [s2, f1.st sCD (by decide)]; exact (he sCD (by simp)).1)
    (by rw [sh2, f1.sh sCD (by decide)]; exact (he sCD (by simp)).2) t2
    (fun y hy => by
      rw [f2.val y (by revert hy; revert y; decide), f1.val y (by revert hy; revert y; decide)]
      exact h.zero y (by revert hy; revert y; decide))
    (by unfold postCap at hcap; omega)
  have st3 : ∀ i, i ∉ [sX, sCD, sY, sY2] → τ3.st i = σ.st i := fun i hi => by
    rw [f3.st i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; tauto), s2,
      f1.st i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; tauto)]
  have sh3 : ∀ i, i ∉ [sX, sCD, sY, sY2] → τ3.sh i = σ.sh i := fun i hi => by
    rw [f3.sh i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; tauto), sh2,
      f1.sh i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; tauto)]
  have v3 : ∀ x, x ∉ [rG, rK1, rM, rD, rT2, rOY, rW] → τ3.val x = σ.val x := fun x hx => by
    rw [f3.val x (by revert hx; revert x; decide), f2.val x (by revert hx; revert x; decide),
      f1.val x (by revert hx; revert x; decide)]
  refine ⟨τ3, WExec.mono (WExec.seq e1 (WExec.seq e2 e3)) le_rfl, ?_⟩
  exact {
    inp := by rw [st3 sIN (by decide), h.inp]
    inph := by rw [sh3 sIN (by decide), h.inph]
    cols := by rw [f3.st sY (by decide), s2, y1, h.y]
    colsh := by rw [f3.sh sY (by decide), sh2, yh1]
    acc := by rw [st3 sACC (by decide)]; exact (he sACC (by simp)).1
    acch := by rw [sh3 sACC (by decide)]; exact (he sACC (by simp)).2
    zd := by rw [st3 sZd (by decide)]; exact (he sZd (by simp)).1
    zdh := by rw [sh3 sZd (by decide)]; exact (he sZd (by simp)).2
    zp := by rw [st3 sZp (by decide)]; exact (he sZp (by simp)).1
    zph := by rw [sh3 sZp (by decide)]; exact (he sZp (by simp)).2
    zg := by rw [st3 sZG (by decide)]; exact (he sZG (by simp)).1
    zgh := by rw [sh3 sZG (by decide)]; exact (he sZG (by simp)).2
    vN := by rw [v3 rN (by decide), h.vN]
    vR := by rw [v3 rR (by decide), h.vR]
    vB := by rw [v3 rB (by decide), h.vB]
    vS := by rw [v3 rS (by decide), h.vS]
    vP := by rw [v3 rP (by decide), h.vP]
    vW := by rw [f3.val rW (by decide), f2.val rW (by decide), w1]
    vM := by rw [f3.val rM (by decide), m2]
    vD := by rw [f3.val rD (by decide), d2]
    vT2 := by rw [f3.val rT2 (by decide), t2]
    vG := g3
    zero := fun x hx => by
      by_cases hK : x = rK1
      · subst hK; rw [f3.val rK1 (by decide), k2]
      · by_cases hO : x = rOY
        · subst hO; rw [f3.val rOY (by decide), f2.val rOY (by decide), oy1]
        · rw [v3 x (by
            simp only [keptRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx ⊢
            exact ⟨hx.2.2.2.2.2.2.2.2.2, hK, hx.2.2.2.2.2.2.1, hx.2.2.2.2.2.2.2.1, hx.2.2.2.2.2.2.2.2.1, hO,
              hx.2.2.2.2.2.1⟩)]
          exact h.zero x (by
            simp only [keptRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx ⊢
            exact ⟨hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1, hx.2.2.2.2.1, hO⟩) }

end NearQuarticWires.StageNativeHeader
