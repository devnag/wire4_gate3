import Proof.Quartic.Reconstruct.ItemBounds

/-!
# One gathered item of a child

Paper: Step 3 of `sec:algorithm`, paper/paper.tex, and `prop:time`.

With the context of the child held in the variables `kM … kPair` and the rates in the store `sF` (`CtxHeld`), and a
width of at least `emitWidth q`, `itemS` reads the gathered item `gatheredItem q x` of a listed system `x` and writes
`frame (systemTag q x) ++ frame (sysWord (systemAt q x))` at depth `1` within `itemCostQ q W` steps
(`itemS_child`). The context stays held.
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces (listWord bitWord)
open NearQuarticWires.Greedy NearQuarticWires.Program

variable {C : Ctx} {B1 B2 : ℕ}

/-- The context of a child held in the state: `M_1`, `A`, `Λ`, `2mG_1`, `2mG_2`, `J`, whether the call has two
circuits, the rates, and the cursors of the rate and digit stores in range. -/
structure CtxHeld (q : ChildRequest B1 B2) (a : DS VV MM) : Prop where
  m1 : a.env kM = q.selected.1.M1
  aa : a.env kA = q.selected.1.A
  lam : a.env kL = q.selected.1.Lambda
  b0 : a.env kB0 = 2 * Algorithm.traceOrder * Builder.occurrences q.call 0
  b1 : a.env kB1 = 2 * Algorithm.traceOrder * Builder.occurrences q.call 1
  jj : a.env kJ = q.cellCall.J
  pair : a.env kPair = if decide (q.call.kind = .pair) then 1 else 0
  fs : a.ram sF = q.selected.1.factors
  rcF : a.rc sF ≤ q.cellCall.J
  rcDp : a.rc sDp ≤ 2 * (q.cellCall.J + 1)
  rcDn : a.rc sDn ≤ 2 * (q.cellCall.J + 1)

/-- The context variables. -/
def ctxVars : List (Fin VV) := [kM, kA, kL, kB0, kB1, kJ, kPair]

theorem CtxHeld.of_fr {q : ChildRequest B1 B2} {a b : DS VV MM} (h : CtxHeld q a) (hfr : ∀ y ∈ ctxVars, b.env y = a.env y)
    (hF : b.ram sF = a.ram sF) (rF : b.rc sF ≤ q.cellCall.J) (rp : b.rc sDp ≤ 2 * (q.cellCall.J + 1))
    (rn : b.rc sDn ≤ 2 * (q.cellCall.J + 1)) : CtxHeld q b :=
  ⟨(hfr kM (by decide)).trans h.m1, (hfr kA (by decide)).trans h.aa, (hfr kL (by decide)).trans h.lam,
    (hfr kB0 (by decide)).trans h.b0, (hfr kB1 (by decide)).trans h.b1, (hfr kJ (by decide)).trans h.jj,
    (hfr kPair (by decide)).trans h.pair, hF.trans h.fs, rF, rp, rn⟩

/-- The cost of one item of a child, uniform over the listed systems. -/
noncomputable def itemCostQ (q : ChildRequest B1 B2) (W : ℕ) : ℕ :=
  itemAxesCost q.cellCall.J W + itemEmitCost W (W - 2) (16 * envelope q + 1) (16 * envelope q + 1)
    (100000 * envelope q ^ 5) + 1

theorem itemEmitCost_mono (W ℓ len0 len1 r L0 L1 R : ℕ) (h0 : len0 ≤ L0) (h1 : len1 ≤ L1) (hr : r ≤ R) :
    itemEmitCost W ℓ len0 len1 r ≤ itemEmitCost W ℓ L0 L1 R := by
  unfold itemEmitCost pointsCost
  have e1 : len1 * (pointCost 2 ℓ + 4) + 8 ≤ L1 * (pointCost 2 ℓ + 4) + 8 :=
    Nat.add_le_add_right (Nat.mul_le_mul_right _ h1) _
  have e2 := Nat.mul_le_mul h0 e1
  have e3 : natBitLength (len0 * len1) ≤ natBitLength (L0 * L1) := natBitLength_mono (Nat.mul_le_mul h0 h1)
  have e4 : emitNatDCost 2 (natBitLength (len0 * len1)) ≤ emitNatDCost 2 (natBitLength (L0 * L1)) := by
    unfold emitNatDCost; exact Nat.mul_le_mul_left _ (by omega)
  have e5 : (5 * r + 1) * (copyCost 2 ℓ + 4) ≤ (5 * R + 1) * (copyCost 2 ℓ + 4) :=
    Nat.mul_le_mul_right _ (by omega)
  omega

/-- **One gathered item of a child.** -/
theorem itemS_child (q : ChildRequest B1 B2) (x : SystemIndex q) (hx : x ∈ systemList q) (a : DS VV MM)
    (hc : Cst a) (rest : List Bool) (hin : C.inp.drop a.ip = gatheredItem q x ++ rest) (h : CtxHeld q a)
    (hW : emitWidth q ≤ C.Wd) :
    Hs C itemS a (itemCostQ q C.Wd)
      (fun b => StMoved a b (gatheredItem q x).length
          (marksD 1 (RepairOrdinary.frame (systemTag q x) ++
            RepairOrdinary.frame (NearCubicGates.Close.Interfaces.Formats.sysWord (systemAt q x)))) itemT ∧
        CtxHeld q b ∧ Cst b) := by
  obtain ⟨-, -, -, hEV, -, hJV, -⟩ := child_le q
  obtain ⟨y1, y2, -, y4⟩ := env_Y q
  have hEW := emitExp_le q
  have hXY := horner_le_env q
  have hS0 := axisData_sum_le q x hx 0
  have hS1 := axisData_sum_le q x hx 1
  have hL0 := axisData_len_le q x.2.2.1 0
  have hL1 := axisData_len_le q x.2.2.1 1
  have hrl := rows_length_le q x
  have hW' : 100000 * (envelope q + 1) ^ 5 + 6 * (envelope q + 1) ^ 2 + 20 ≤ C.Wd := hW
  set V := envelope q with hV
  set E := emitExp q with hE
  set Y := (V + 1) ^ (V + 2) with hY
  have hVW : 100000 * V ^ 5 + 2 ≤ C.Wd := by
    have : V ^ 5 ≤ (V + 1) ^ 5 := Nat.pow_le_pow_left (by omega) 5
    omega
  have hEW' : 2 * E + 2 ≤ C.Wd := hEW.trans hW
  have h2E : 2 ^ E ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hEE : 2 ^ E * 2 ^ E ≤ 2 ^ C.Wd := by
    rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hY1 : (V + 1) ^ (V + 1) ≤ Y := Nat.pow_le_pow_right (by omega) (by omega)
  have hVY : V + 1 ≤ Y := le_trans (by nlinarith) y2
  have hlt : ∀ v, v < 256 * Y → v < 2 ^ E := fun v hv => lt_of_lt_of_le hv y4
  have hbits : ∀ v, v < 256 * Y → natBitLength v ≤ C.Wd - 2 := fun v hv =>
    (natBitLength_le_emitExp q (hlt v hv)).trans (by omega)
  have hin' : C.inp.drop a.ip = bitWord x.1 ++ (listWord NearCubicGates.Close.Interfaces.intWord
      (List.ofFn (x.2.2.1 0) ++ List.ofFn (x.2.2.1 1)) ++ (listWord rowWord (systemAt q x).rows ++ rest)) := by
    rw [hin]; unfold gatheredItem; rw [digits_flatten]; simp only [List.append_assoc]
  have hsq : (axisData q x.2.2.1 0).1 + (axisData q x.2.2.1 0).2.1 + (axisData q x.2.2.1 0).2.2 +
      (axisData q x.2.2.1 1).1 + (axisData q x.2.2.1 1).2.1 + (axisData q x.2.2.1 1).2.2 + 1 < 2 ^ E :=
    hlt _ (by omega)
  have hprod : (axisData q x.2.2.1 0).2.1 * (axisData q x.2.2.1 1).2.1 < 256 * Y := by
    have h1 : (axisData q x.2.2.1 0).2.1 * (axisData q x.2.2.1 1).2.1 ≤ (16 * V + 1) * (16 * V + 1) :=
      Nat.mul_le_mul hL0 hL1
    have h2 : (16 * V + 1) * (16 * V + 1) < 256 * ((V + 1) ^ 2) := by ring_nf; omega
    have h3 : 256 * ((V + 1) ^ 2) ≤ 256 * Y := Nat.mul_le_mul_left _ y2
    omega
  refine (itemS_spec a hc x.1 (List.ofFn (x.2.2.1 0) ++ List.ofFn (x.2.2.1 1)) (systemAt q x).rows rest hin' q.selected.1.M1 q.selected.1.A
    q.selected.1.Lambda (2 * Algorithm.traceOrder * Builder.occurrences q.call 0)
    (2 * Algorithm.traceOrder * Builder.occurrences q.call 1) q.cellCall.J q.call.n q.selected.1.hE
    (decide (q.call.kind = .pair)) q.selected.1.factors h.m1 h.aa h.lam h.b0 h.b1 h.jj h.pair (one_le_A q)
    (one_le_Lambda q) h.fs (by rw [factors_length]) h.rcF (fun i _ => factors_getD_le q i) (digits_length q x.2.2.1)
    (digits_natAbs_le q x hx) ⟨h.rcDp, h.rcDn⟩ (lt_of_lt_of_le (itemBig_lt q 0) h2E)
    (lt_of_lt_of_le (itemBig_lt q 1) h2E)
    (lt_of_lt_of_le (hlt _ (show (q.selected.1.hE + 1) * (q.call.n + 1) ^ q.cellCall.J < 256 * Y by omega)) h2E)
    (by have := hbits q.selected.1.hE (by omega); omega)
    (by have := hbits (2 * (q.cellCall.J + 1)) (by omega); omega) (by omega)
    (axisData q x.2.2.1 0) (axisData q x.2.2.1 1) (axisTriple_zero q x.2.2.1).symm (axisTriple_one q x.2.2.1).symm
    (C.Wd - 2)
    (systemAt_rows_two q x) (by rw [pow_two]; exact lt_of_lt_of_le (Nat.mul_self_lt_mul_self hsq) hEE)
    (hbits _ (by omega)) (hbits _ (by omega)) (by omega) (hbits _ hprod)
    (fun v hv => (rows_natBitLength_le q x v hv).trans (by rw [← hV]; omega))
    (lt_of_le_of_lt (show 5 * (systemAt q x).rows.length ≤ C.Wd by omega) Nat.lt_two_pow_self)).mono ?_
    (fun b ⟨m, r1, r2, r3, c⟩ => ⟨?_, ?_, c⟩)
  · have := itemEmitCost_mono C.Wd (C.Wd - 2) _ _ (systemAt q x).rows.length (16 * V + 1) (16 * V + 1)
      (100000 * V ^ 5) hL0 hL1 (by omega)
    unfold itemCostQ
    rw [← hV]
    omega
  · rw [itemWord_eq q x hx] at m
    have hl : (bitWord x.1 ++ listWord NearCubicGates.Close.Interfaces.intWord
        (List.ofFn (x.2.2.1 0) ++ List.ofFn (x.2.2.1 1)) ++
        listWord rowWord (systemAt q x).rows).length = (gatheredItem q x).length := by
      unfold gatheredItem; rw [digits_flatten]
    rw [hl] at m
    exact m
  · exact h.of_fr (fun y hy => m.fr y (by revert hy y; decide)) (m.ram sF (by decide) (by decide)) r3 r1 r2

end NearQuarticWires.Reconstruct
