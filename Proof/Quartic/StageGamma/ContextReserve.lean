import Proof.Quartic.StageGamma.OutputFrame

set_option autoImplicit false

namespace NearQuarticWires.StageGamma

open NearCubicGates.Close.Cells

/-- `prop:time`, paper/paper.tex: changing the
fixed Gaussian-call reserves charges the actual larger reset and input
budgets, while all binary arithmetic uses the same physical word width. -/
theorem OpEx.enlarge_reserves {V M : ℕ} (width : ℕ) (input : List Bool)
    (L B L' B' : ℕ) (hL : L ≤ L') (hB : B ≤ B')
    {o : Op V M} {a b : DS V M} {k : ℕ}
    (h : OpEx (gaussContext width input L B) o a b k) :
    ∃ k', OpEx (gaussContext width input L' B') o a b k' ∧
      k' ≤ k * (1 + L' + B') := by
  cases h with
  | kem bit a h =>
    exact ⟨1, OpEx.kem bit a (h.trans_le hL), by omega⟩
  | kcall s a hs hb =>
    exact ⟨1 + L' + B', OpEx.kcall (C := gaussContext width input L' B') s a hs
      (show compactGaussCallee.bud s ≤ B' from hb.trans hB), by nlinarith⟩
  | zero x a => exact ⟨1, OpEx.zero x a, by omega⟩
  | inc x a h => exact ⟨1, OpEx.inc x a h, by omega⟩
  | add x y a h1 h2 => exact ⟨1, OpEx.add x y a h1 h2, by omega⟩
  | sub x y a h1 h2 => exact ⟨1, OpEx.sub x y a h1 h2, by omega⟩
  | copy x y a h => exact ⟨1, OpEx.copy x y a h, by omega⟩
  | half x a => exact ⟨1, OpEx.half x a, by omega⟩
  | shl x a h => exact ⟨1, OpEx.shl x a h, by omega⟩
  | mul x y z a h1 h2 h3 h4 => exact ⟨1, OpEx.mul x y z a h1 h2 h3 h4, by omega⟩
  | dm x y q r a h1 h2 h3 h4 h5 h6 h7 h8 =>
    exact ⟨1, OpEx.dm x y q r a h1 h2 h3 h4 h5 h6 h7 h8, by omega⟩
  | rdI x a h => exact ⟨1, OpEx.rdI x a h, by omega⟩
  | bkI a h => exact ⟨1, OpEx.bkI a h, by omega⟩
  | emit bit a => exact ⟨1, OpEx.emit bit a, by omega⟩
  | rdM m x a h => exact ⟨1, OpEx.rdM m x a h, by omega⟩
  | wrM m x a h => exact ⟨1, OpEx.wrM m x a h, by omega⟩
  | rwM m a => exact ⟨_, OpEx.rwM m a, by nlinarith⟩
  | srtM m a h => exact ⟨_, OpEx.srtM m a h, by nlinarith⟩
  | rdK x a h => exact ⟨1, OpEx.rdK x a h, by omega⟩

/-- `prop:time`, paper/paper.tex: the same actual
finite program runs with compiler-compatible larger Gaussian reserves,
with a fully charged polynomial factor and identical computed output. -/
theorem Ex.enlarge_reserves {V M : ℕ} (width : ℕ) (input : List Bool)
    (L B L' B' : ℕ) (hL : L ≤ L') (hB : B ≤ B')
    {s : St V M} {a b : DS V M} {k : ℕ}
    (h : Ex (gaussContext width input L B) s a b k) :
    ∃ k', Ex (gaussContext width input L' B') s a b k' ∧
      k' ≤ k * (1 + L' + B') := by
  let R := 1 + L' + B'
  have hR : 1 ≤ R := by dsimp [R]; omega
  induction h with
  | op h =>
    obtain ⟨k, hk, hb⟩ := OpEx.enlarge_reserves width input L B L' B' hL hB h
    exact ⟨k, Ex.op hk, hb⟩
  | seq h1 h2 ih1 ih2 =>
    obtain ⟨k1, hk1, hb1⟩ := ih1
    obtain ⟨k2, hk2, hb2⟩ := ih2
    exact ⟨_, Ex.seq hk1 hk2, by nlinarith⟩
  | iteT hc he h ih =>
    obtain ⟨k, hk, hb⟩ := ih
    exact ⟨_, Ex.iteT hc he hk, by nlinarith⟩
  | iteF hc he h ih =>
    obtain ⟨k, hk, hb⟩ := ih
    exact ⟨_, Ex.iteF hc he hk, by nlinarith⟩
  | loopF hc he => exact ⟨2, Ex.loopF hc he, by nlinarith⟩
  | loopT hc he h1 h2 ih1 ih2 =>
    obtain ⟨k1, hk1, hb1⟩ := ih1
    obtain ⟨k2, hk2, hb2⟩ := ih2
    exact ⟨_, Ex.loopT hc he hk1 hk2, by nlinarith⟩
  | mono h hm ih =>
    obtain ⟨k, hk, hb⟩ := ih
    exact ⟨k, hk, hb.trans (Nat.mul_le_mul_right _ hm)⟩

end NearQuarticWires.StageGamma
