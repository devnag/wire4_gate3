import Proof.Gates.Tabulator.Print
import Proof.Wire_3_5.CompilerTable

set_option autoImplicit false

namespace NearQuarticWires.Cells
open NearCubicWires NearCubicWires.ThresholdCompiler
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Compiler
open NearCubicGates.Close.Tabulator

/-- `lem:print`, paper/paper.tex: the explicit child cap for an n-input atom. -/
def childCap (n B : ℕ) : ℕ := n * (B + Nat.clog 2 n + 3)

/-- `lem:print`, paper/paper.tex: the input-height logarithm fits the printed cap. -/
theorem clog_succ_le (n : ℕ) : Nat.clog 2 (n + 1) ≤ Nat.clog 2 n + 1 := by
  apply Nat.clog_le_of_le_pow
  have hn := Nat.le_pow_clog (by norm_num : 1 < 2) n
  have hp := Nat.one_le_two_pow (n := Nat.clog 2 n)
  rw [pow_succ]
  omega

/-- `imp:disjoint` and `lem:print`, paper/paper.tex: the actual disjoint
children of the inclusive gate obey n(B + ceil(log₂ n) + 3), including ties. -/
theorem exactChildren_length_childCap {n : ℕ} (hn : 0 < n) (B : ℕ)
    (g : NormalizedThresholdGate n) (hg : GateBits B g) :
    (exactChildren g).length ≤ childCap n B := by
  have hs : Nat.size (compilerInputHeight g.weight (g.threshold - 1)) ≤ blockBits n B :=
    Nat.size_le.mpr (height_bound B g hg)
  refine (disjointCrossingChildren_encodingLength g.weight (g.threshold - 1)).trans ?_
  apply max_le
  · unfold childCap
    have : 1 ≤ B + Nat.clog 2 n + 3 := by omega
    nlinarith
  · apply (Nat.mul_le_mul_left n hs).trans
    apply Nat.mul_le_mul_left
    unfold blockBits
    have := clog_succ_le n
    omega

/-- `imp:pullback`, paper/paper.tex: convert an exact child without changing any parameter. -/
def childGate {n : ℕ} (e : ExactEquation n) : ExactThresholdGate n := ⟨e.weights, e.target⟩

/-- `imp:pullback`, paper/paper.tex: exact children pulled back through the actual separated coordinates. -/
def separatedChildren {n : ℕ} {ZL ZR : Type} (C : HalfCoords n ZL ZR)
    (g : NormalizedThresholdGate n) : List (SeparatedEquation ZL ZR) :=
  (exactChildren g).map (fun e => pullChild C (childGate e))

/-- `lem:print`, paper/paper.tex: inclusive threshold atoms equal the integer sum of child indicators. -/
theorem separatedChildren_sum {n : ℕ} {ZL ZR : Type} (C : HalfCoords n ZL ZR)
    (g : NormalizedThresholdGate n) (zl : ZL) (zr : ZR) :
    ((separatedChildren C g).map fun e => bitZ (e.holds zl zr)).sum =
      bitZ (g.eval (C.point zl zr)) := by
  have h := exactChildren_sum g (C.point zl zr)
  unfold separatedChildren
  rw [List.map_map]
  trans ((exactChildren g).map fun e => testValue e (C.point zl zr)).sum
  · congr 1
    apply List.map_congr_left
    intro e _
    simp only [Function.comp_apply, pullChild_holds, childGate, ExactThresholdGate.eval, bitZ,
      testValue, ExactEquation.Holds, bitInt, decide_eq_true_eq]
  · exact h

/-- `lem:print`, paper/paper.tex: pullback preserves the literal number of children. -/
theorem separatedChildren_length {n : ℕ} {ZL ZR : Type} (C : HalfCoords n ZL ZR)
    (g : NormalizedThresholdGate n) : (separatedChildren C g).length = (exactChildren g).length := by
  simp [separatedChildren]

/-- `imp:stack` and `lem:print`, paper/paper.tex: explicit uniform integer value envelope. -/
theorem separatedChildren_abs_le {n : ℕ} {ZL ZR : Type} (C : HalfCoords n ZL ZR)
    (g : NormalizedThresholdGate n) (B : ℕ) (hg : GateBits B g)
    (e : SeparatedEquation ZL ZR) (he : e ∈ separatedChildren C g) (zl : ZL) (zr : ZR) :
    |eqValue e zl zr| ≤ ((n + 1) * childBound n B : ℕ) := by
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
  have hb := exactChildren_params B g hg a ha
  refine (pullChild_abs_le C (childGate a) zl zr).trans ?_
  have ht : |a.target| ≤ (childBound n B : ℤ) := by
    rw [Int.abs_eq_natAbs]; exact_mod_cast hb.2
  have hw : ∑ i, |a.weights i| ≤ (n : ℤ) * childBound n B := by
    calc ∑ i, |a.weights i| ≤ ∑ _i : Fin n, (childBound n B : ℤ) := by
          apply Finset.sum_le_sum
          intro i _
          rw [Int.abs_eq_natAbs]
          exact_mod_cast hb.1 i
      _ = _ := by simp
  dsimp only [childGate]
  push_cast
  nlinarith

end NearQuarticWires.Cells
