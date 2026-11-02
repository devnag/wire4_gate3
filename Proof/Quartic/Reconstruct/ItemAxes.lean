import Proof.Quartic.Reconstruct.ReadList
import Proof.Quartic.Reconstruct.TagProgram

/-!
# The box of one gathered item

Paper: Step 3 of `sec:algorithm`, paper/paper.tex, and `lem:certify`(d).

A gathered item starts with the part `s` and the digit vector `δ` (`SystemsSplit.gatheredItem`). `itemAxesS` reads
them (`itemReadS_spec`: the part into `gS`, the positive and the negative parts of the digits into the stores `sDp`,
`sDn`) and computes the two coordinate intervals of the box of `δ` into `pLo0 … pB1` (`itemAxesS_spec`): the first by
`axisOneS kB0`, the second by `axisOneS kB1` when the call has two circuits and `(0, 1, 0)` otherwise.
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces (listWord bitWord)

variable {C : Ctx}

/-- The interval data `(lo', len, B)` of one coordinate from `M_1`, `A`, `Λ`, `B` and the two Horner values
(`BoxArith.boxAxisOf_eq`). -/
def axisTriple (M A L B Hp Hn : ℕ) : ℕ × ℕ × ℕ :=
  ((M * Hp + A + A * B - (M * Hn + L)) / A,
    min ((M * Hp + (L - 1) + A * B + A - M * Hn) / A) (2 * B + 1) - (M * Hp + A + A * B - (M * Hn + L)) / A, B)

/-- The positive part of digit `p + i` of a digit list. -/
def posDig (ds : List ℤ) (p i : ℕ) : ℕ := (ds.getD (p + i) 0).toNat

/-- The negative part of digit `p + i` of a digit list. -/
def negDig (ds : List ℤ) (p i : ℕ) : ℕ := (-(ds.getD (p + i) 0)).toNat

/-- The effect of a phase of one item: the input cursor advances by `k`, the output grows by `w`, the stores other
than the digit stores are unchanged, the cursors other than those of the digit stores and of the rates are unchanged,
and only the variables in `T` change. -/
structure StMoved (a b : DS VV MM) (k : ℕ) (w : List Bool) (T : List (Fin VV)) : Prop where
  ip : b.ip = a.ip + k
  out : b.out = a.out ++ w
  ram : ∀ m, m ≠ sDp → m ≠ sDn → b.ram m = a.ram m
  rc : ∀ m, m ≠ sDp → m ≠ sDn → m ≠ sF → b.rc m = a.rc m
  kin : b.kin = a.kin
  kout : b.kout = a.kout
  kc : b.kc = a.kc
  fr : Fr a b T

theorem StMoved.trans {a b c : DS VV MM} {k k' : ℕ} {w w' : List Bool} {T : List (Fin VV)} (h1 : StMoved a b k w T)
    (h2 : StMoved b c k' w' T) : StMoved a c (k + k') (w ++ w') T :=
  ⟨by rw [h2.ip, h1.ip, Nat.add_assoc], by rw [h2.out, h1.out, List.append_assoc],
    fun m p1 p2 => (h2.ram m p1 p2).trans (h1.ram m p1 p2), fun m p1 p2 p3 => (h2.rc m p1 p2 p3).trans (h1.rc m p1 p2 p3),
    h2.kin.trans h1.kin, h2.kout.trans h1.kout, h2.kc.trans h1.kc, Fr.trans h1.fr h2.fr⟩

theorem StMoved.weaken {a b : DS VV MM} {k : ℕ} {w : List Bool} {T T' : List (Fin VV)} (h : StMoved a b k w T)
    (hT : ∀ y ∈ T, y ∈ T') : StMoved a b k w T' :=
  ⟨h.ip, h.out, h.ram, h.rc, h.kin, h.kout, h.kc, h.fr.weaken hT⟩

theorem StMoved.of_moved {a b : DS VV MM} {k : ℕ} {w : List Bool} {T : List (Fin VV)} (h : Moved a b k w T) :
    StMoved a b k w T :=
  ⟨h.ip, h.out, fun m _ _ => by rw [h.ram], fun m _ _ _ => by rw [h.rc], h.kin, h.kout, h.kc, h.fr⟩

/-- Read the part and the digit vector of an item; rewind the digit stores. -/
def itemReadS : St VV MM :=
  .seq rdNatI (.seq (.op (.copy gS t3)) (.seq (.op (.rwM sDp)) (.seq (.op (.rwM sDn)) (.seq digitsS
    (.seq (.op (.rwM sDp)) (.op (.rwM sDn)))))))

/-- The variables written while computing the box of an item. -/
def itemAxesT : List (Fin VV) := [t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, vJ, gS, dN, dK, dS, vN, vH, vI, vT, vR,
  aHp, aHn, aM, aA, aL, aB, vLo, vLen, xP1, xP2, xP3, xX, xY, xR, xQ, xC, pLo0, pLen0, pB0, pLo1, pLen1, pB1]

theorem natBitLength_bit (s : Bool) : natBitLength (if s then 1 else 0) = 1 := by
  cases s <;> simp [natBitLength]

/-- **Reading an item's part and digits.** -/
theorem itemReadS_spec (a : DS VV MM) (hc : Cst a) (s : Bool) (ds : List ℤ) (rest : List Bool)
    (hin : C.inp.drop a.ip = bitWord s ++ (listWord NearCubicGates.Close.Interfaces.intWord ds ++ rest))
    (hW : ∀ z ∈ ds, natBitLength z.natAbs + 2 ≤ C.Wd) (hWl : natBitLength ds.length + 2 ≤ C.Wd) (hW3 : 3 ≤ C.Wd)
    (K : ℕ) (hK : a.rc sDp ≤ K ∧ a.rc sDn ≤ K) :
    Hs C itemReadS a (2 * K + ds.length * (60 * C.Wd + 88) + 40 * C.Wd + 120)
      (fun b => b.env gS = (if s then 1 else 0) ∧ b.rc sDp = 0 ∧ b.rc sDn = 0 ∧
        (∀ i < ds.length, (b.ram sDp).getD i 0 = (ds.getD i 0).toNat ∧
          (b.ram sDn).getD i 0 = (-(ds.getD i 0)).toNat) ∧
        ds.length ≤ (b.ram sDp).length ∧ ds.length ≤ (b.ram sDn).length ∧ b.rc sF = a.rc sF ∧
        StMoved a b (bitWord s ++ listWord NearCubicGates.Close.Interfaces.intWord ds).length [] itemAxesT ∧
        Cst b) := by
  have hb1 := natBitLength_bit s
  have hin' : C.inp.drop a.ip = natWord (if s then 1 else 0) ++
      (listWord NearCubicGates.Close.Interfaces.intWord ds ++ rest) := hin
  refine Hx.hs (Hs.then (rdNatI_spec a hc (if s then 1 else 0) _ hin' (by omega))
    (fun b0 ⟨r1, _, r3, r4, r5⟩ n0 hn0 => ?_))
  simp only [Prod.mk.injEq] at r4
  obtain ⟨o0, m0, q0, i0, k0, kc0⟩ := r4
  refine Hs.then (hs_copy C gS t3 b0 (by decide)) (fun b1 hb1' n1 hn1 => ?_)
  subst hb1'
  refine Hs.then (hs_rwM C sDp _) (fun b2 hb2 n2 hn2 => ?_)
  subst hb2
  refine Hs.then (hs_rwM C sDn _) (fun b3 hb3 n3 hn3 => ?_)
  subst hb3
  have hne : sDn ≠ sDp := sDp_ne_sDn.symm
  set b3 := ((b0.set gS (b0.env t3)).rew sDp).rew sDn with hb3
  have c3 : Cst b3 := ⟨by vsimp [hb3, DS.rew_env, Cst.of_fr hc r5 (by decide) |>.z],
    by vsimp [hb3, DS.rew_env, Cst.of_fr hc r5 (by decide) |>.one],
    by vsimp [hb3, DS.rew_env, Cst.of_fr hc r5 (by decide) |>.two]⟩
  have ip3 : b3.ip = a.ip + (natWord (if s then 1 else 0)).length := by
    rw [hb3, DS.rew_ip, DS.rew_ip, DS.set_ip, r3]
  have hin3 : C.inp.drop b3.ip = listWord NearCubicGates.Close.Interfaces.intWord ds ++ rest := by
    rw [ip3, ← List.drop_drop, hin', List.drop_left]
  have rc3p : b3.rc sDp = 0 := by rw [hb3, DS.rew_rc_ne _ sDp_ne_sDn, DS.rew_rc_self]
  have rc3n : b3.rc sDn = 0 := by rw [hb3, DS.rew_rc_self]
  have hd3 : DigitsIn b3 0 ds 0 :=
    ⟨rc3p, rc3n, Nat.zero_le _, Nat.zero_le _, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  refine Hs.then (digitsS_spec b3 c3 ds rest hin3 hW hWl 0 hd3) (fun b4 ⟨d4, m4, c4⟩ n4 hn4 => ?_)
  refine Hs.then (hs_rwM C sDp b4) (fun b5 hb5 n5 hn5 => ?_)
  subst hb5
  refine Hs.last (hs_rwM C sDn _) (fun b6 hb6 n6 hn6 => ?_)
  subst hb6
  obtain ⟨e1, e2, e3, e4, e5⟩ := d4
  have hT1 : ∀ y ∈ rdNatT, y ∈ itemAxesT := by decide
  have hT2 : ∀ y ∈ digitsT, y ∈ itemAxesT := by decide
  have hsF : sF ≠ sDp ∧ sF ≠ sDn := by decide
  refine ⟨⟨?_, ?_, ?_, fun i hi => ?_, ?_, ?_, ?_, ⟨?_, ?_, fun m h1 h2 => ?_, fun m h1 h2 h3 => ?_, ?_, ?_, ?_, ?_⟩,
    ⟨c4.z, c4.one, c4.two⟩⟩, ?_⟩
  · rw [DS.rew_env, DS.rew_env, m4.fr gS (by decide), hb3, DS.rew_env, DS.rew_env, DS.set_env_self, r1]
  · rw [DS.rew_rc_ne _ sDp_ne_sDn, DS.rew_rc_self]
  · rw [DS.rew_rc_self]
  · simpa using e5 i hi
  · simpa using e3
  · simpa using e4
  · rw [DS.rew_rc_ne _ hsF.2, DS.rew_rc_ne _ hsF.1, m4.rc sF hsF.1 hsF.2, hb3, DS.rew_rc_ne _ hsF.2,
      DS.rew_rc_ne _ hsF.1, DS.set_rc, q0]
  · rw [DS.rew_ip, DS.rew_ip, m4.ip, ip3, List.length_append]
    unfold bitWord
    omega
  · rw [DS.rew_out, DS.rew_out, m4.out, hb3, DS.rew_out, DS.rew_out, DS.set_out, o0, List.append_nil]
  · rw [DS.rew_ram, DS.rew_ram, m4.ram m h1 h2, hb3, DS.rew_ram, DS.rew_ram, DS.set_ram, m0]
  · rw [DS.rew_rc_ne _ h2, DS.rew_rc_ne _ h1, m4.rc m h1 h2, hb3, DS.rew_rc_ne _ h2, DS.rew_rc_ne _ h1, DS.set_rc,
      q0]
  · rw [DS.rew_kin, DS.rew_kin, m4.kin, hb3, DS.rew_kin, DS.rew_kin, DS.set_kin, i0]
  · rw [DS.rew_kout, DS.rew_kout, m4.kout, hb3, DS.rew_kout, DS.rew_kout, DS.set_kout, k0]
  · rw [DS.rew_kc, DS.rew_kc, m4.kc, hb3, DS.rew_kc, DS.rew_kc, DS.set_kc, kc0]
  · have f1 : Fr a b0 itemAxesT := r5.weaken hT1
    have f2 : Fr b0 b3 itemAxesT := fun y hy => by
      rw [hb3, DS.rew_env, DS.rew_env, DS.set_env_ne _ _ (fun h => hy (by rw [h]; decide))]
    have f3 : Fr b3 b4 itemAxesT := m4.fr.weaken hT2
    intro y hy
    rw [DS.rew_env, DS.rew_env]
    exact (f1.trans (f2.trans f3)) y hy
  · have c2 : n2 ≤ K + 1 := by
      have := hn2; simp only [DS.set_rc, q0] at this; omega
    have c3 : n3 ≤ K + 1 := by
      have := hn3; simp only [DS.rew_rc_ne _ hne, DS.set_rc, q0] at this; omega
    have c5 : n5 ≤ ds.length + 1 := by
      have := hn5; rw [e1] at this; omega
    have c6 : n6 ≤ ds.length + 1 := by
      have := hn6; rw [DS.rew_rc_ne _ hne, e2] at this; omega
    have c0 : n0 ≤ 60 := by rw [hb1] at hn0; omega
    have hr : ds.length * (60 * C.Wd + 88) = ds.length * (60 * C.Wd + 84) + 4 * ds.length := by ring
    omega

end NearQuarticWires.Reconstruct
