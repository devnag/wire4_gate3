import Proof.Quartic.Reconstruct.ItemAxes

/-!
# The two coordinate intervals of one item

Paper: Step 3 of `sec:algorithm`, paper/paper.tex, and `lem:certify`(d).

`axisCopyS kB lo len bb` runs `axisOneS kB` and keeps `(lo', len, B)` in `lo`, `len`, `bb` (`axisCopyS_spec`);
`itemAxesS` reads the part and the digit vector of an item and computes both coordinate intervals of its box
(`itemAxesS_spec`), the second one `(0, 1, 0)` for a call with one circuit.
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces (listWord bitWord)

variable {C : Ctx}

/-- One coordinate interval, kept in `lo`, `len`, `bb`. -/
def axisCopyS (kB lo len bb : Fin VV) : St VV MM :=
  .seq (axisOneS kB) (.seq (.op (.copy lo vLo)) (.seq (.op (.copy len vLen)) (.op (.copy bb aB))))

theorem axisCopyS_spec (kB lo len bb : Fin VV) (hkB : kB ∉ axisOneT ∧ kB ≠ kM ∧ kB ≠ kA ∧ kB ≠ kL ∧ kB ≠ kJ)
    (hd : lo ∉ axisOneT ∧ len ∉ axisOneT ∧ bb ∉ axisOneT ∧ len ≠ lo ∧ bb ≠ lo ∧ bb ≠ len)
    (hd' : vZ ∉ [lo, len, bb] ∧ v1 ∉ [lo, len, bb] ∧ v2 ∉ [lo, len, bb]) (T : List (Fin VV)) (hT : ∀ y ∈ axisOneT, y ∈ T) (hT' : lo ∈ T ∧ len ∈ T ∧ bb ∈ T)
    (a : DS VV MM) (hc : Cst a) (M A L B N p R D : ℕ) (hM : a.env kM = M) (hA : a.env kA = A)
    (hL : a.env kL = L) (hB : a.env kB = B) (hN : a.env kJ = N) (hA1 : 1 ≤ A) (hL1 : 1 ≤ L)
    (hFl : N ≤ (a.ram sF).length) (hrcF : a.rc sF ≤ N)
    (hp : a.rc sDp = p ∧ a.rc sDn = p) (hDl : p + N < (a.ram sDp).length ∧ p + N < (a.ram sDn).length)
    (hRb : ∀ i < N, (a.ram sF).getD i 0 ≤ R)
    (hDb : ∀ i ≤ N, storeDig (a.ram sDp) p i ≤ D ∧ storeDig (a.ram sDn) p i ≤ D)
    (hbig : 2 * (M * ((D + 1) * (R + 1) ^ N) + M * ((D + 1) * (R + 1) ^ N) + A * B + A + L + 2 * B + 2) <
      2 ^ C.Wd) (hX : (D + 1) * (R + 1) ^ N < 2 ^ C.Wd) (hNW : N < 2 ^ C.Wd) :
    Hs C (axisCopyS kB lo len bb) a (N * 30 + 106)
      (fun b => (b.env lo, b.env len, b.env bb) = axisTriple M A L B
          (hornerN (storeDig (a.ram sF) 0) (storeDig (a.ram sDp) p) N)
          (hornerN (storeDig (a.ram sF) 0) (storeDig (a.ram sDn) p) N) ∧
        b.rc sDp = p + N + 1 ∧ b.rc sDn = p + N + 1 ∧ b.rc sF ≤ N ∧ b.ram = a.ram ∧ StMoved a b 0 [] T ∧
        Cst b) := by
  obtain ⟨hlo, hlen, hbb, n1, n2, n3⟩ := hd
  refine Hx.hs (Hs.then (axisOneS_spec kB hkB a hc M A L B N p R D hM hA hL hB hN hA1 hL1 hFl hrcF hp hDl hRb hDb
    hbig hX hNW) (fun b0 ⟨y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15⟩ k0 hk0 => ?_))
  refine Hs.then (hs_copy C lo vLo b0 (fun h => hlo (by rw [h]; decide))) (fun b1 hb1 k1 hk1 => ?_)
  subst hb1
  refine Hs.then (hs_copy C len vLen _ (fun h => hlen (by rw [h]; decide))) (fun b2 hb2 k2 hk2 => ?_)
  subst hb2
  refine Hs.last (hs_copy C bb aB _ (fun h => hbb (by rw [h]; decide))) (fun b3 hb3 k3 hk3 => ?_)
  subst hb3
  have vLenlo : vLen ≠ lo := fun h => hlo (by rw [← h]; decide)
  have aBlo : aB ≠ lo := fun h => hlo (by rw [← h]; decide)
  have aBlen : aB ≠ len := fun h => hlen (by rw [← h]; decide)
  have fr3 : Fr b0 (((b0.set lo (b0.env vLo)).set len ((b0.set lo (b0.env vLo)).env vLen)).set bb
      (((b0.set lo (b0.env vLo)).set len ((b0.set lo (b0.env vLo)).env vLen)).env aB)) [lo, len, bb] := by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    rw [DS.set_env_ne _ _ hy.2.2, DS.set_env_ne _ _ hy.2.1, DS.set_env_ne _ _ hy.1]
  refine ⟨⟨?_, y4, y5, y7, y8, ⟨by simp [y9], by simp [y10], fun m _ _ => by simp [y8], fun m h1 h2 h3 => by
    simp [y6 m h1 h2 h3], by simp [y11], by simp [y12], by simp [y13], ?_⟩, Cst.of_fr y15 fr3 hd'⟩, by omega⟩
  · unfold axisTriple
    simp only [DS.set_env_self, DS.set_env_ne _ _ n1.symm, DS.set_env_ne _ _ n2.symm, DS.set_env_ne _ _ n3.symm,
      DS.set_env_ne _ _ vLenlo, DS.set_env_ne _ _ aBlo, DS.set_env_ne _ _ aBlen, y1, y2, y3]
  · intro y hy
    have h1 : y ≠ lo := fun h => hy (h ▸ hT'.1)
    have h2 : y ≠ len := fun h => hy (h ▸ hT'.2.1)
    have h3 : y ≠ bb := fun h => hy (h ▸ hT'.2.2)
    rw [DS.set_env_ne _ _ h3, DS.set_env_ne _ _ h2, DS.set_env_ne _ _ h1]
    exact y14 y (fun h => hy (hT y h))

/-- The second coordinate interval: computed when the call has two circuits, `(0, 1, 0)` otherwise. -/
def axisPairS : St VV MM :=
  .ite (.eq kPair v1) (axisCopyS kB1 pLo1 pLen1 pB1)
    (.seq (.op (.zero pLo1)) (.seq (.op (.copy pLen1 v1)) (.op (.zero pB1))))

/-- The variables written by `axisPairS`. -/
def axisPairT : List (Fin VV) := axisOneT ++ [pLo1, pLen1, pB1]

/-- Read the part and the digit vector of an item and compute both coordinate intervals of its box. -/
def itemAxesS : St VV MM :=
  .seq itemReadS (.seq (axisCopyS kB0 pLo0 pLen0 pB0) axisPairS)

/-- The cost of `itemAxesS` with `N = J` and width `W`. -/
def itemAxesCost (N W : ℕ) : ℕ := (2 * N + 2) * (60 * W + 88) + 40 * W + 64 * N + 340

theorem toNat_le_of_natAbs_le {z : ℤ} {D : ℕ} (h : z.natAbs ≤ D) : z.toNat ≤ D ∧ (-z).toNat ≤ D := by
  omega

theorem getD_parts_le {ds : List ℤ} {D : ℕ} (hDb : ∀ z ∈ ds, z.natAbs ≤ D) (j : ℕ) :
    (ds.getD j 0).toNat ≤ D ∧ (-(ds.getD j 0)).toNat ≤ D := by
  rw [List.getD_eq_getElem?_getD]
  cases hj : ds[j]? with
  | none => simp
  | some v => exact toNat_le_of_natAbs_le (hDb v (List.mem_of_getElem? hj))

/-- **The box of one item.** -/
theorem itemAxesS_spec (a : DS VV MM) (hc : Cst a) (s : Bool) (ds : List ℤ) (rest : List Bool)
    (hin : C.inp.drop a.ip = bitWord s ++ (listWord NearCubicGates.Close.Interfaces.intWord ds ++ rest))
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
    (hlW : natBitLength (2 * (N + 1)) + 2 ≤ C.Wd) (hW3 : 3 ≤ C.Wd) :
    Hs C itemAxesS a (itemAxesCost N C.Wd)
      (fun b => b.env gS = (if s then 1 else 0) ∧
        (b.env pLo0, b.env pLen0, b.env pB0) = axisTriple M A L B0
          (hornerN (fun i => Fs.getD i 0) (posDig ds 0) N) (hornerN (fun i => Fs.getD i 0) (negDig ds 0) N) ∧
        (b.env pLo1, b.env pLen1, b.env pB1) = (if pr then axisTriple M A L B1
          (hornerN (fun i => Fs.getD i 0) (posDig ds (N + 1)) N)
          (hornerN (fun i => Fs.getD i 0) (negDig ds (N + 1)) N) else (0, 1, 0)) ∧
        b.rc sDp ≤ 2 * (N + 1) ∧ b.rc sDn ≤ 2 * (N + 1) ∧ b.rc sF ≤ N ∧
        StMoved a b (bitWord s ++ listWord NearCubicGates.Close.Interfaces.intWord ds).length [] itemAxesT ∧
        Cst b) := by
  have hW : ∀ z ∈ ds, natBitLength z.natAbs + 2 ≤ C.Wd := fun z hz =>
    le_trans (Nat.add_le_add_right (natBitLength_mono (hDb z hz)) 2) hDW
  have hNW : N < 2 ^ C.Wd := lt_of_lt_of_le (lt_of_lt_of_le (by omega : N < 2 * (N + 1)) (lt_natBitLength _).le)
    (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hWl : natBitLength ds.length + 2 ≤ C.Wd := by rw [hds]; exact hlW
  refine Hx.hs (Hs.then (itemReadS_spec a hc s ds rest hin hW hWl hW3 (2 * (N + 1)) hK)
    (fun b0 ⟨g0, p0, q0, v0, l0, l0', rF0, m0, c0⟩ k0 hk0 => ?_))
  have kv : ∀ y, y ∉ itemAxesT → b0.env y = a.env y := m0.fr
  have hF0 : b0.ram sF = Fs := by rw [m0.ram sF (by decide) (by decide), hF]
  have hrc0 : b0.rc sF ≤ N := by rw [rF0]; exact hrcF
  have hsF : storeDig (b0.ram sF) 0 = fun i => Fs.getD i 0 := by
    funext i; rw [hF0]; unfold storeDig; rw [Nat.zero_add]
  have hD0 : ∀ q i, q + i < 2 * (N + 1) → storeDig (b0.ram sDp) q i = posDig ds q i ∧
      storeDig (b0.ram sDn) q i = negDig ds q i := fun q i hi => by
    unfold storeDig posDig negDig
    exact v0 (q + i) (by omega)
  have hDb0 : ∀ q, q ≤ N + 1 → ∀ i ≤ N, storeDig (b0.ram sDp) q i ≤ D ∧ storeDig (b0.ram sDn) q i ≤ D := by
    intro q hq i hi
    rw [(hD0 q i (by omega)).1, (hD0 q i (by omega)).2]
    exact getD_parts_le hDb (q + i)
  have hRb0 : ∀ i < N, (b0.ram sF).getD i 0 ≤ R := fun i hi => by rw [hF0]; exact hRb i hi
  have hFl0 : N ≤ (b0.ram sF).length := by rw [hF0]; exact hFl
  have hDl0 : ∀ q, q ≤ N + 1 → q + N < (b0.ram sDp).length ∧ q + N < (b0.ram sDn).length := fun q hq =>
    ⟨by omega, by omega⟩
  have hZ : ∀ y ∈ axisOneT ++ [pLo0, pLen0, pB0], y ∈ itemAxesT := by decide
  refine Hs.then (axisCopyS_spec kB0 pLo0 pLen0 pB0 (by decide) (by decide) (by decide) (axisOneT ++ [pLo0, pLen0, pB0])
    (by decide) (by decide) b0 c0 M A L B0
    N 0 R D (by rw [kv kM (by decide), hM]) (by rw [kv kA (by decide), hA]) (by rw [kv kL (by decide), hL])
    (by rw [kv kB0 (by decide), hB0]) (by rw [kv kJ (by decide), hN]) hA1 hL1 hFl0 hrc0 ⟨p0, q0⟩ (hDl0 0 (by omega))
    hRb0 (hDb0 0 (by omega)) hbig0 hX hNW) (fun b1 ⟨x1, r1, s1, f1, e1, m1, c1⟩ k1 hk1 => ?_)
  have kv1 : ∀ y, y ∉ itemAxesT → b1.env y = a.env y := fun y hy =>
    (m1.fr y (fun h => hy (hZ y h))).trans (kv y hy)
  have hH0 : ∀ q, q + N < 2 * (N + 1) →
      hornerN (storeDig (b0.ram sF) 0) (storeDig (b0.ram sDp) q) N =
        hornerN (fun i => Fs.getD i 0) (posDig ds q) N ∧
      hornerN (storeDig (b0.ram sF) 0) (storeDig (b0.ram sDn) q) N =
        hornerN (fun i => Fs.getD i 0) (negDig ds q) N := fun q hq => by
    rw [hsF]
    exact ⟨hornerN_congr _ _ _ _ N (fun _ _ => rfl) (fun i hi => (hD0 q i (by omega)).1),
      hornerN_congr _ _ _ _ N (fun _ _ => rfl) (fun i hi => (hD0 q i (by omega)).2)⟩
  rw [(hH0 0 (by omega)).1, (hH0 0 (by omega)).2] at x1
  -- the second coordinate
  have hpair : Hs C axisPairS b1 (N * 30 + 107)
      (fun b => (b.env pLo1, b.env pLen1, b.env pB1) = (if pr then axisTriple M A L B1
          (hornerN (fun i => Fs.getD i 0) (posDig ds (N + 1)) N)
          (hornerN (fun i => Fs.getD i 0) (negDig ds (N + 1)) N) else (0, 1, 0)) ∧
        (b.env pLo0, b.env pLen0, b.env pB0) = (b1.env pLo0, b1.env pLen0, b1.env pB0) ∧
        b.rc sDp ≤ 2 * (N + 1) ∧ b.rc sDn ≤ 2 * (N + 1) ∧ b.rc sF ≤ N ∧ StMoved b1 b 0 [] axisPairT ∧ Cst b) := by
    have hpv : b1.env kPair = if pr then 1 else 0 := by rw [kv1 kPair (by decide), hpr]
    refine Hs.ite (show kPair ≠ v1 by decide) (fun he => ?_) (fun he => ?_)
    · have hp : pr = true := by
        cases pr
        · simp [Cnd.eval, hpv, c1.one] at he
        · rfl
      subst hp
      have hb1F : b1.ram sF = b0.ram sF := by rw [e1]
      refine (axisCopyS_spec kB1 pLo1 pLen1 pB1 (by decide) (by decide) (by decide) axisPairT (by decide) (by decide) b1 c1
        M A L B1 N
        (N + 1) R D (by rw [kv1 kM (by decide), hM]) (by rw [kv1 kA (by decide), hA])
        (by rw [kv1 kL (by decide), hL]) (by rw [kv1 kB1 (by decide), hB1]) (by rw [kv1 kJ (by decide), hN]) hA1 hL1
        (by rw [e1]; exact hFl0) f1 ⟨by omega, by omega⟩ (by rw [e1]; exact hDl0 (N + 1) le_rfl)
        (by rw [e1]; exact hRb0) (by rw [e1]; exact hDb0 (N + 1) le_rfl) hbig1 hX hNW).mono (by omega)
        (fun b ⟨x2, r2, s2, f2, e2, m2, c2⟩ => ⟨?_, ?_, by omega, by omega, f2, m2, c2⟩)
      · rw [x2, e1, (hH0 (N + 1) (by omega)).1, (hH0 (N + 1) (by omega)).2]
        rfl
      · rw [m2.fr pLo0 (by decide), m2.fr pLen0 (by decide), m2.fr pB0 (by decide)]
    · have hp : pr = false := by
        cases pr
        · rfl
        · simp [Cnd.eval, hpv, c1.one] at he
      subst hp
      refine Hx.hs (Hs.then (hs_zero C pLo1 b1) (fun d1 hd1 j1 hj1 => ?_))
      subst hd1
      refine Hs.then (hs_copy C pLen1 v1 _ (by decide)) (fun d2 hd2 j2 hj2 => ?_)
      subst hd2
      refine Hs.last (hs_zero C pB1 _) (fun d3 hd3 j3 hj3 => ?_)
      subst hd3
      refine ⟨⟨?_, ?_, by simp [r1], by simp [s1], by simp [f1], ⟨by simp, by simp, fun m _ _ => rfl,
        fun m _ _ _ => rfl, rfl, rfl, rfl, ?_⟩, ⟨by vsimp [c1.z], by vsimp [c1.one], by vsimp [c1.two]⟩⟩, by omega⟩
      · vsimp [c1.one]
      · vsimp [c1.z]
      · intro y hy
        have h1 : y ≠ pLo1 := fun h => hy (by rw [h]; decide)
        have h2 : y ≠ pLen1 := fun h => hy (by rw [h]; decide)
        have h3 : y ≠ pB1 := fun h => hy (by rw [h]; decide)
        rw [DS.set_env_ne _ _ h3, DS.set_env_ne _ _ h2, DS.set_env_ne _ _ h1]
  refine Hs.last hpair (fun b2 ⟨x2, y2, r2, s2, f2, m2, c2⟩ k2 hk2 => ?_)
  refine ⟨⟨?_, by rw [y2, x1], x2, r2, s2, f2, ?_, c2⟩, ?_⟩
  · rw [m2.fr gS (by decide), m1.fr gS (by decide), g0]
  · have := (m0.trans (m1.weaken hZ)).trans (m2.weaken (by decide))
    simpa using this
  · unfold itemAxesCost
    have hr : (2 * N + 2) * (60 * C.Wd + 88) = 2 * (N + 1) * (60 * C.Wd + 88) := by ring
    rw [hds] at hk0
    omega

end NearQuarticWires.Reconstruct
