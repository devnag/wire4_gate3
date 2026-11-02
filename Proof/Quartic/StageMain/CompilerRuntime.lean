import Proof.Gates.Cells.Run

/-!
# Polynomial overhead of compiling the main arithmetic program

`prop:time`, paper/paper.tex, counts ordinary
bit operations. This bound expands the actual cell-language setup,
compiled instruction costs and teardown; the source clock and input
length occur only linearly, with polynomial finite-width overhead.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.Runtime

open NearCubicGates.Close.Cells

def compilerMajorant (S I N : ℕ) : ℕ :=
  ((30 * S + 20) + 4 * S + (S * (60 * S + 11 * S + 8) + 7 * S + 3) +
    4 * S + (S * (60 * S + 11 * S + 8) + 7 * S + 3) +
    4 * S + (S * (60 * S + 11 * S + 8) + 7 * S + 3) +
    (18 * S + 3) + (18 * S + 3) + (18 * S + 3) + 4 * 3 + 10 + 1 +
    ((S + 2) * (50 * S + 10 + 1) + S * (1 + 1) + (40 * S + 10) +
      (40 * (S + S + S + 3) + 10) + 3 + 1 +
      ((3 * S + 1) + (3 * S + 1) + (3 * S + 1) + (3 * S + 1) +
        (3 * (S + S + S + 3) + 1) + 4))) + 1 +
    (N * (500 * (S + 1) ^ 2 + 100 * (S + 3)) + 1 +
      (10 * I + 5 * N + 10 * S + 5 * (S + 3) + S * (5 * ((2 * S + 1) * N) + 2) + 10))

theorem compilerMajorant_le (S I N : ℕ) (hS : 1 ≤ S) :
    compilerMajorant S I N ≤ 10000 * S ^ 2 * (N + I + 1) := by
  have hS2 : S ≤ S ^ 2 := by nlinarith
  have hNS := Nat.mul_le_mul_left N hS2
  have hIS : I ≤ S ^ 2 * I := by
    have hh : 1 ≤ S ^ 2 := by nlinarith
    simpa using Nat.mul_le_mul_right I hh
  have hN : N ≤ S ^ 2 * N := by
    have hh : 1 ≤ S ^ 2 := by nlinarith
    simpa using Nat.mul_le_mul_right N hh
  unfold compilerMajorant
  nlinarith only [hS, hS2, hNS, hIS, hN, Nat.zero_le (S ^ 2 * I), Nat.zero_le (S ^ 2 * N)]

theorem langBudget_le (K : Callee) (z : Sz) (V M : ℕ) (input : List Bool) (N S : ℕ)
    (hS : 1 ≤ S) (hV : V ≤ S) (hM : M ≤ S) (hK : TSK K ≤ S)
    (ha1 : z.a1 ≤ S) (hc1 : z.c1 ≤ S) (ha2 : z.a2 ≤ S) (hc2 : z.c2 ≤ S)
    (ha3 : z.a3 ≤ S) (hc3 : z.c3 ≤ S)
    (hL : leadOnes input ≤ S) (hW : z.W (leadOnes input) ≤ S)
    (hLk : z.Lk (leadOnes input) ≤ S) (hBk : z.Bk (leadOnes input) ≤ S) :
    langBudget K z V M input N ≤ 10000 * S ^ 2 * (N + input.length + 1) := by
  apply le_trans (b := compilerMajorant S input.length N) ?_ (compilerMajorant_le _ _ _ hS)
  unfold langBudget costA costB costC compilerMajorant
  dsimp only
  gcongr

end NearQuarticWires.StageMain.Runtime
