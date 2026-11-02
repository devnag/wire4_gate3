import Proof.Quartic.Reconstruct.ItemBox
import Proof.Quartic.Reconstruct.ItemEmit

/-!
# One gathered item, written as one system

Paper: Step 3 of `sec:algorithm`, paper/paper.tex.

`itemS` reads one gathered item `bitWord s ++ listWord intWord δ ++ listWord rowWord rows` and writes the framed tag
and the framed word of its system at depth `1` (`itemS_spec`): the box by `itemAxesS` (`ItemBox.itemAxesS_spec`),
then the tag, the points and the copied rows by `itemEmitS` (`ItemEmit.itemEmitS_spec`).
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces (listWord bitWord)

variable {C : Ctx}

/-- Read one gathered item and write its system. -/
def itemS : St VV MM := .seq itemAxesS itemEmitS

/-- The variables written by `itemS`. -/
def itemT : List (Fin VV) := itemAxesT ++ itemEmitT

/-- **One item.** -/
theorem itemS_spec (a : DS VV MM) (hc : Cst a) (s : Bool) (ds : List ℤ) (rows : List (ℕ × List ℕ × ℕ))
    (rest : List Bool)
    (hin : C.inp.drop a.ip = bitWord s ++ (listWord NearCubicGates.Close.Interfaces.intWord ds ++
      (listWord rowWord rows ++ rest)))
    (M A L B0 B1 N R D : ℕ) (pr : Bool) (Fs : List ℕ)
    (hM : a.env kM = M) (hA : a.env kA = A) (hL : a.env kL = L) (hB0 : a.env kB0 = B0) (hB1 : a.env kB1 = B1)
    (hN : a.env kJ = N) (hpr : a.env kPair = if pr then 1 else 0) (hA1 : 1 ≤ A) (hL1 : 1 ≤ L)
    (hF : a.ram sF = Fs) (hFl : N ≤ Fs.length) (hrcF : a.rc sF ≤ N) (hRb : ∀ i < N, Fs.getD i 0 ≤ R)
    (hds : ds.length = 2 * (N + 1)) (hDb : ∀ z ∈ ds, z.natAbs ≤ D)
    (hK : a.rc sDp ≤ 2 * (N + 1) ∧ a.rc sDn ≤ 2 * (N + 1))
    (hbig0 : 2 * (M * ((D + 1) * (R + 1) ^ N) + M * ((D + 1) * (R + 1) ^ N) + A * B0 + A + L + 2 * B0 + 2) <
      2 ^ C.Wd)
    (hbig1 : 2 * (M * ((D + 1) * (R + 1) ^ N) + M * ((D + 1) * (R + 1) ^ N) + A * B1 + A + L + 2 * B1 + 2) <
      2 ^ C.Wd)
    (hX : (D + 1) * (R + 1) ^ N < 2 ^ C.Wd) (hDW : natBitLength D + 2 ≤ C.Wd)
    (hlW : natBitLength (2 * (N + 1)) + 2 ≤ C.Wd) (hW3 : 3 ≤ C.Wd)
    (T0 T1 : ℕ × ℕ × ℕ)
    (hT0 : T0 = axisTriple M A L B0 (hornerN (fun i => Fs.getD i 0) (posDig ds 0) N)
      (hornerN (fun i => Fs.getD i 0) (negDig ds 0) N))
    (hT1 : T1 = if pr then axisTriple M A L B1 (hornerN (fun i => Fs.getD i 0) (posDig ds (N + 1)) N)
      (hornerN (fun i => Fs.getD i 0) (negDig ds (N + 1)) N) else (0, 1, 0))
    (ℓ : ℕ) (h2 : ∀ row ∈ rows, row.2.1.length = 2)
    (hbigE : (T0.1 + T0.2.1 + T0.2.2 + T1.1 + T1.2.1 + T1.2.2 + 1) ^ 2 < 2 ^ C.Wd)
    (hfit0 : natBitLength (T0.1 + T0.2.1 + T0.2.2) ≤ ℓ) (hfit1 : natBitLength (T1.1 + T1.2.1 + T1.2.2) ≤ ℓ)
    (hℓ : ℓ + 2 ≤ C.Wd) (hprod : natBitLength (T0.2.1 * T1.2.1) ≤ ℓ)
    (hrows : ∀ v ∈ rows.length :: rows.flatMap rowNats, natBitLength v ≤ ℓ) (hNW : 5 * rows.length < 2 ^ C.Wd) :
    Hs C itemS a (itemAxesCost N C.Wd + itemEmitCost C.Wd ℓ T0.2.1 T1.2.1 rows.length + 1)
      (fun b => StMoved a b (bitWord s ++ listWord NearCubicGates.Close.Interfaces.intWord ds ++
          listWord rowWord rows).length (marksD 1 (itemWord s T0.1 T0.2.1 T0.2.2 T1.1 T1.2.1 T1.2.2 rows)) itemT ∧
        b.rc sDp ≤ 2 * (N + 1) ∧ b.rc sDn ≤ 2 * (N + 1) ∧ b.rc sF ≤ N ∧ Cst b) := by
  refine Hs.seq (itemAxesS_spec a hc s ds (listWord rowWord rows ++ rest) hin M A L B0 B1 N R D pr Fs hM hA hL hB0
    hB1 hN hpr hA1 hL1 hF hFl hrcF hRb hds hDb hK hbig0 hbig1 hX hDW hlW hW3)
    (fun b ⟨g1, x0, x1, r1, s1, f1, m1, c1⟩ => ?_)
  rw [← hT0] at x0
  rw [← hT1] at x1
  simp only [Prod.ext_iff] at x0 x1
  obtain ⟨e0, e1, e2⟩ := x0
  obtain ⟨e3, e4, e5⟩ := x1
  have hinb : C.inp.drop b.ip = listWord rowWord rows ++ rest := by
    rw [m1.ip, ← List.drop_drop, hin, ← List.append_assoc, List.drop_left]
  refine (itemEmitS_spec b c1 hW3 s g1 ℓ rows rest hinb h2 (by rw [e0, e1, e2, e3, e4, e5]; exact hbigE)
    (by rw [e0, e1, e2]; exact hfit0) (by rw [e3, e4, e5]; exact hfit1) hℓ (by rw [e1, e4]; exact hprod) hrows
    hNW).mono (by rw [e1, e4]) (fun d ⟨m2, c2⟩ => ⟨?_, ?_, ?_, ?_, c2⟩)
  · rw [e0, e1, e2, e3, e4, e5] at m2
    have := m1.weaken (T' := itemT) (fun y hy => List.mem_append_left _ hy) |>.trans
      ((StMoved.of_moved m2).weaken (fun y hy => List.mem_append_right _ hy))
    simpa [List.length_append, Nat.add_assoc] using this
  · rw [m2.rc]; exact r1
  · rw [m2.rc]; exact s1
  · rw [m2.rc]; exact f1

end NearQuarticWires.Reconstruct
