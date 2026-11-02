import Proof.Quartic.Reconstruct.AxisProgram
import Proof.Quartic.Reconstruct.DigitsProgram

/-!
# One coordinate interval from the stored digits

Paper: `lem:certify`(d), paper/paper.tex.

`axisOneS kB` runs Horner's scheme on the positive and the negative parts of the next `J + 1` stored digits (stores
`sDp`, `sDn`) with the rates of the store `sF`, and then the interval program `axisS` with `M_1`, `A`, `Λ` and the
bound held in `kB` (`axisOneS_spec`).
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearCubicGates.Close.Cells

variable {C : Ctx}

/-- The store of the rates (the factor list of the parameters). -/
def sF : Fin MM := ⟨0, by decide⟩
/-- The context: `M_1`. -/
def kM : Fin VV := ⟨70, by decide⟩
/-- The context: `A`. -/
def kA : Fin VV := ⟨71, by decide⟩
/-- The context: `Λ`. -/
def kL : Fin VV := ⟨72, by decide⟩
/-- The context: `2mG_1`. -/
def kB0 : Fin VV := ⟨73, by decide⟩
/-- The context: `2mG_2`. -/
def kB1 : Fin VV := ⟨74, by decide⟩
/-- The context: the last digit index `J`. -/
def kJ : Fin VV := ⟨75, by decide⟩
/-- The context: `1` when the call has two circuits. -/
def kPair : Fin VV := ⟨76, by decide⟩

/-- The interval of one coordinate from the next stored digits. -/
def axisOneS (kB : Fin VV) : St VV MM :=
  .seq (.op (.rwM sF)) (.seq (.op (.copy vN kJ)) (.seq (hornerS sDp sF) (.seq (.op (.copy aHp vH))
  (.seq (.op (.rwM sF)) (.seq (hornerS sDn sF) (.seq (.op (.copy aHn vH)) (.seq (.op (.copy aM kM))
  (.seq (.op (.copy aA kA)) (.seq (.op (.copy aL kL)) (.seq (.op (.copy aB kB)) axisS))))))))))

/-- The variables written by `axisOneS`. -/
def axisOneT : List (Fin VV) := [vN, vH, vI, vT, vR, aHp, aHn, aM, aA, aL, aB, vLo, vLen, xP1, xP2, xP3, xX, xY, xR,
  xQ, xC]

@[simp] theorem DS.rew_env (a : DS VV MM) (m : Fin MM) : (a.rew m).env = a.env := rfl
@[simp] theorem DS.rew_ram (a : DS VV MM) (m : Fin MM) : (a.rew m).ram = a.ram := rfl
@[simp] theorem DS.rew_ip (a : DS VV MM) (m : Fin MM) : (a.rew m).ip = a.ip := rfl
@[simp] theorem DS.rew_out (a : DS VV MM) (m : Fin MM) : (a.rew m).out = a.out := rfl
@[simp] theorem DS.rew_kin (a : DS VV MM) (m : Fin MM) : (a.rew m).kin = a.kin := rfl
@[simp] theorem DS.rew_kout (a : DS VV MM) (m : Fin MM) : (a.rew m).kout = a.kout := rfl
@[simp] theorem DS.rew_kc (a : DS VV MM) (m : Fin MM) : (a.rew m).kc = a.kc := rfl
theorem DS.rew_rc_self (a : DS VV MM) (m : Fin MM) : (a.rew m).rc m = 0 := by simp [DS.rew]
theorem DS.rew_rc_ne (a : DS VV MM) {m m' : Fin MM} (h : m' ≠ m) : (a.rew m).rc m' = a.rc m' := by
  simp [DS.rew, Function.update_of_ne h]

theorem getD_le_of_forall {l : List ℕ} {D : ℕ} (h : ∀ v ∈ l, v ≤ D) (i : ℕ) : l.getD i 0 ≤ D := by
  rw [List.getD_eq_getElem?_getD]
  cases hi : l[i]? with
  | none => simp
  | some v => simpa using h v (List.mem_of_getElem? hi)

theorem horner_fit (Fs Ds : ℕ → ℕ) (R D N : ℕ) (hF : ∀ i, Fs i ≤ R) (hD : ∀ i, Ds i ≤ D) (i : ℕ) (hi : i < N) :
    Fs i * hornerN Fs Ds i + Ds (i + 1) ≤ (D + 1) * (R + 1) ^ N := by
  have h1 := hornerN_le Fs Ds R D hF hD i
  have h2 : Fs i * hornerN Fs Ds i ≤ R * ((D + 1) * (R + 1) ^ i) := Nat.mul_le_mul (hF i) h1
  have h3 : (R + 1) ^ (i + 1) ≤ (R + 1) ^ N := Nat.pow_le_pow_right (by omega) hi
  have h4 := hD (i + 1)
  have h5 : 1 ≤ (R + 1) ^ i := Nat.one_le_pow _ _ (by omega)
  have h6 : (D + 1) * (R + 1) ^ (i + 1) ≤ (D + 1) * (R + 1) ^ N := Nat.mul_le_mul_left _ h3
  rw [pow_succ] at h6
  nlinarith

/-- **One coordinate interval.** With the rates in `sF`, the digits of one circuit at the common cursor `p` of `sDp`
and `sDn`, and `M_1`, `A`, `Λ`, `B`, `J` in the context, `axisOneS kB` leaves the shifted start and the number of
points of the interval in `vLo`, `vLen`, and `B` in `aB`; the digit cursors advance by `J + 1`. -/
theorem axisOneS_spec (kB : Fin VV) (hkB : kB ∉ axisOneT ∧ kB ≠ kM ∧ kB ≠ kA ∧ kB ≠ kL ∧ kB ≠ kJ)
    (a : DS VV MM) (hc : Cst a) (M A L B N p R D : ℕ) (hM : a.env kM = M) (hA : a.env kA = A)
    (hL : a.env kL = L) (hB : a.env kB = B) (hN : a.env kJ = N) (hA1 : 1 ≤ A) (hL1 : 1 ≤ L)
    (hFl : N ≤ (a.ram sF).length) (hrcF : a.rc sF ≤ N)
    (hp : a.rc sDp = p ∧ a.rc sDn = p) (hDl : p + N < (a.ram sDp).length ∧ p + N < (a.ram sDn).length)
    (hRb : ∀ i < N, (a.ram sF).getD i 0 ≤ R)
    (hDb : ∀ i ≤ N, storeDig (a.ram sDp) p i ≤ D ∧ storeDig (a.ram sDn) p i ≤ D)
    (hbig : 2 * (M * ((D + 1) * (R + 1) ^ N) + M * ((D + 1) * (R + 1) ^ N) + A * B + A + L + 2 * B + 2) <
      2 ^ C.Wd) (hX : (D + 1) * (R + 1) ^ N < 2 ^ C.Wd) (hNW : N < 2 ^ C.Wd) :
    Hs C (axisOneS kB) a (N * 30 + 100)
      (fun b => b.env vLo = (M * hornerN (storeDig (a.ram sF) 0) (storeDig (a.ram sDp) p) N + A + A * B -
          (M * hornerN (storeDig (a.ram sF) 0) (storeDig (a.ram sDn) p) N + L)) / A ∧
        b.env vLen = min ((M * hornerN (storeDig (a.ram sF) 0) (storeDig (a.ram sDp) p) N + (L - 1) + A * B + A -
            M * hornerN (storeDig (a.ram sF) 0) (storeDig (a.ram sDn) p) N) / A) (2 * B + 1) -
          (M * hornerN (storeDig (a.ram sF) 0) (storeDig (a.ram sDp) p) N + A + A * B -
            (M * hornerN (storeDig (a.ram sF) 0) (storeDig (a.ram sDn) p) N + L)) / A ∧
        b.env aB = B ∧ b.rc sDp = p + N + 1 ∧ b.rc sDn = p + N + 1 ∧
        (∀ m, m ≠ sDp → m ≠ sDn → m ≠ sF → b.rc m = a.rc m) ∧ b.rc sF ≤ N ∧
        b.ram = a.ram ∧ b.ip = a.ip ∧ b.out = a.out ∧ b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧
        Fr a b axisOneT ∧ Cst b) := by
  -- clamped rates and digits, equal to the stored ones where Horner's scheme reads them
  let Fc : ℕ → ℕ := fun i => if i < N then storeDig (a.ram sF) 0 i else 0
  let Pc : ℕ → ℕ := fun i => if i ≤ N then storeDig (a.ram sDp) p i else 0
  let Nc : ℕ → ℕ := fun i => if i ≤ N then storeDig (a.ram sDn) p i else 0
  have hFd : ∀ i, Fc i ≤ R := fun i => by
    show (if i < N then storeDig (a.ram sF) 0 i else 0) ≤ R
    split
    · have := hRb i (by assumption); simpa [storeDig] using this
    · exact Nat.zero_le _
  have hDp : ∀ i, Pc i ≤ D := fun i => by
    show (if i ≤ N then storeDig (a.ram sDp) p i else 0) ≤ D
    split
    · exact (hDb i (by assumption)).1
    · exact Nat.zero_le _
  have hDn : ∀ i, Nc i ≤ D := fun i => by
    show (if i ≤ N then storeDig (a.ram sDn) p i else 0) ≤ D
    split
    · exact (hDb i (by assumption)).2
    · exact Nat.zero_le _
  have hcp : ∀ k ≤ N, hornerN (storeDig (a.ram sF) 0) (storeDig (a.ram sDp) p) k = hornerN Fc Pc k := fun k hk =>
    hornerN_congr _ _ _ _ k (fun i hi => by show _ = if i < N then _ else _; rw [if_pos (by omega)])
      (fun i hi => by show _ = if i ≤ N then _ else _; rw [if_pos (by omega)])
  have hcn : ∀ k ≤ N, hornerN (storeDig (a.ram sF) 0) (storeDig (a.ram sDn) p) k = hornerN Fc Nc k := fun k hk =>
    hornerN_congr _ _ _ _ k (fun i hi => by show _ = if i < N then _ else _; rw [if_pos (by omega)])
      (fun i hi => by show _ = if i ≤ N then _ else _; rw [if_pos (by omega)])
  set Hp := hornerN (storeDig (a.ram sF) 0) (storeDig (a.ram sDp) p) N with hHp
  set Hn := hornerN (storeDig (a.ram sF) 0) (storeDig (a.ram sDn) p) N with hHn
  have hHp_le : Hp ≤ (D + 1) * (R + 1) ^ N := by rw [hHp, hcp N le_rfl]; exact hornerN_le _ _ R D hFd hDp N
  have hHn_le : Hn ≤ (D + 1) * (R + 1) ^ N := by rw [hHn, hcn N le_rfl]; exact hornerN_le _ _ R D hFd hDn N
  have hne1 : sDp ≠ sF := by decide
  have hne2 : sDn ≠ sF := by decide
  have hT : ∀ y ∈ hornerT, y ∈ axisOneT := by decide
  have hxT : ∀ y ∈ axisT, y ∈ axisOneT := by decide
  -- rewind the rates
  refine Hx.hs (Hs.then (hs_rwM C sF a) (fun b0 hb0 n0 hn0 => ?_))
  subst hb0
  refine Hs.then (hs_copy C vN kJ _ (by decide)) (fun b1 hb1 n1 hn1 => ?_)
  subst hb1
  set s1 := (a.rew sF).set vN ((a.rew sF).env kJ) with hs1
  have s1ram : s1.ram = a.ram := rfl
  have s1F : s1.rc sF = 0 := by rw [hs1, DS.set_rc, DS.rew_rc_self]
  have s1Dp : s1.rc sDp = p := by rw [hs1, DS.set_rc, DS.rew_rc_ne _ hne1, hp.1]
  have s1Dn : s1.rc sDn = p := by rw [hs1, DS.set_rc, DS.rew_rc_ne _ hne2, hp.2]
  have c1 : Cst s1 := ⟨by vsimp [hs1, DS.rew_env, hc.z], by vsimp [hs1, DS.rew_env, hc.one],
    by vsimp [hs1, DS.rew_env, hc.two]⟩
  have hfitp : ∀ i < N, (s1.ram sF).getD (s1.rc sF + i) 0 *
      hornerN (storeDig (s1.ram sF) (s1.rc sF)) (storeDig (s1.ram sDp) (s1.rc sDp)) i +
      storeDig (s1.ram sDp) (s1.rc sDp) (i + 1) < 2 ^ C.Wd := by
    intro i hi
    rw [s1ram, s1F, s1Dp, hcp i hi.le]
    have hf := horner_fit _ _ R D N hFd hDp i hi
    have e1 : Fc i = (a.ram sF).getD (0 + i) 0 := by show (if i < N then _ else 0) = _; rw [if_pos hi]; rfl
    have e2 : Pc (i + 1) = storeDig (a.ram sDp) p (i + 1) := by
      show (if i + 1 ≤ N then _ else 0) = _; rw [if_pos (by omega)]
    rw [e1, e2] at hf
    exact lt_of_le_of_lt hf hX
  refine Hs.then (hornerS_spec sDp sF hne1 s1 c1 N (by vsimp [hs1, DS.rew_env, hN]) (by rw [s1Dp, s1ram]; exact hDl.1)
    (by rw [s1F, s1ram]; omega) hfitp hNW) (fun b2 ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12⟩ n2 hn2 => ?_)
  rw [s1ram, s1F, s1Dp] at g1
  refine Hs.then (hs_copy C aHp vH b2 (by decide)) (fun b3 hb3 n3 hn3 => ?_)
  subst hb3
  refine Hs.then (hs_rwM C sF _) (fun b4 hb4 n4 hn4 => ?_)
  subst hb4
  set s4 := (b2.set aHp (b2.env vH)).rew sF with hs4
  have s4ram : s4.ram = a.ram := by rw [hs4, DS.rew_ram, DS.set_ram, g5, s1ram]
  have s4F : s4.rc sF = 0 := by rw [hs4, DS.rew_rc_self]
  have s4Dn : s4.rc sDn = p := by
    rw [hs4, DS.rew_rc_ne _ hne2, DS.set_rc, g4 sDn (by decide) hne2, s1Dn]
  have c4 : Cst s4 := ⟨by vsimp [hs4, DS.rew_env, g12.z], by vsimp [hs4, DS.rew_env, g12.one],
    by vsimp [hs4, DS.rew_env, g12.two]⟩
  have s4N : s4.env vN = N := by
    rw [hs4, DS.rew_env, DS.set_env_ne _ _ (by decide), g11 vN (by decide)]; vsimp [hs1, DS.rew_env, hN]
  have hfitn : ∀ i < N, (s4.ram sF).getD (s4.rc sF + i) 0 *
      hornerN (storeDig (s4.ram sF) (s4.rc sF)) (storeDig (s4.ram sDn) (s4.rc sDn)) i +
      storeDig (s4.ram sDn) (s4.rc sDn) (i + 1) < 2 ^ C.Wd := by
    intro i hi
    rw [s4ram, s4F, s4Dn, hcn i hi.le]
    have hf := horner_fit _ _ R D N hFd hDn i hi
    have e1 : Fc i = (a.ram sF).getD (0 + i) 0 := by show (if i < N then _ else 0) = _; rw [if_pos hi]; rfl
    have e2 : Nc (i + 1) = storeDig (a.ram sDn) p (i + 1) := by
      show (if i + 1 ≤ N then _ else 0) = _; rw [if_pos (by omega)]
    rw [e1, e2] at hf
    exact lt_of_le_of_lt hf hX
  refine Hs.then (hornerS_spec sDn sF hne2 s4 c4 N s4N (by rw [s4Dn, s4ram]; exact hDl.2)
    (by rw [s4F, s4ram]; omega) hfitn hNW) (fun b5 ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12⟩ n5 hn5 => ?_)
  rw [s4ram, s4F, s4Dn] at f1
  -- the values kept so far
  have hkB' := hkB.1
  have kpre : ∀ y, y ∉ axisOneT → b5.env y = a.env y := by
    intro y hy
    have hy1 : y ∉ hornerT := fun h => hy (hT y h)
    rw [f11 y hy1, hs4, DS.rew_env, DS.set_env_ne _ _ (fun h => hy (by rw [h]; decide)), g11 y hy1, hs1,
      DS.set_env_ne _ _ (fun h => hy (by rw [h]; decide)), DS.rew_env]
  have b5Hp : b5.env aHp = Hp := by
    rw [f11 aHp (by decide), hs4, DS.rew_env, DS.set_env_self, g1]
  refine Hs.then (hs_copy C aHn vH b5 (by decide)) (fun b6 hb6 n6 hn6 => ?_)
  subst hb6
  refine Hs.then (hs_copy C aM kM _ (by decide)) (fun b7 hb7 n7 hn7 => ?_)
  subst hb7
  refine Hs.then (hs_copy C aA kA _ (by decide)) (fun b8 hb8 n8 hn8 => ?_)
  subst hb8
  refine Hs.then (hs_copy C aL kL _ (by decide)) (fun b9 hb9 n9 hn9 => ?_)
  subst hb9
  refine Hs.then (hs_copy C aB kB _ (fun h => hkB' (by rw [← h]; decide))) (fun b10 hb10 n10 hn10 => ?_)
  subst hb10
  have eM : b5.env kM = M := by rw [kpre kM (by decide), hM]
  have eA : b5.env kA = A := by rw [kpre kA (by decide), hA]
  have eL : b5.env kL = L := by rw [kpre kL (by decide), hL]
  have eB : b5.env kB = B := by rw [kpre kB hkB', hB]
  have hkBM := hkB.2.1
  have hkBA := hkB.2.2.1
  have hkBL := hkB.2.2.2.1
  set b10 := ((((b5.set aHn (b5.env vH)).set aM ((b5.set aHn (b5.env vH)).env kM)).set aA _).set aL _).set aB _
    with hb10
  have c10 : Cst b10 := ⟨by vsimp [hb10, f12.z], by vsimp [hb10, f12.one], by vsimp [hb10, f12.two]⟩
  have x1 : b10.env aM = M := by
    rw [hb10]; vsimp [eM]
  have x2 : b10.env aA = A := by
    rw [hb10]; vsimp [eA]
  have x3 : b10.env aL = L := by
    rw [hb10]; vsimp [eL]
  have nL : kB ≠ aL := fun h => hkB' (by rw [h]; decide)
  have nA : kB ≠ aA := fun h => hkB' (by rw [h]; decide)
  have nM : kB ≠ aM := fun h => hkB' (by rw [h]; decide)
  have nHn : kB ≠ aHn := fun h => hkB' (by rw [h]; decide)
  have x4 : b10.env aB = B := by
    rw [hb10, DS.set_env_self, DS.set_env_ne _ _ nL, DS.set_env_ne _ _ nA, DS.set_env_ne _ _ nM,
      DS.set_env_ne _ _ nHn, eB]
  have x5 : b10.env aHp = Hp := by rw [hb10]; vsimp [b5Hp]
  have x6 : b10.env aHn = Hn := by rw [hb10]; vsimp [f1]; rfl
  have hbig' : 2 * (M * Hp + M * Hn + A * B + A + L + 2 * B + 2) < 2 ^ C.Wd := by
    have m1 := Nat.mul_le_mul_left M hHp_le
    have m2 := Nat.mul_le_mul_left M hHn_le
    omega
  refine Hs.last (axisS_spec b10 c10 M A L B Hp Hn x1 x2 x3 x4 x5 x6 hA1 hL1 hbig')
    (fun b11 ⟨y1, y2, y3, y4, y5⟩ n11 hn11 => ?_)
  have hrc10 : ∀ m, b10.rc m = b5.rc m := fun m => by rw [hb10]; simp
  have hram10 : b10.ram = b5.ram := by rw [hb10]; simp
  refine ⟨⟨y1, y2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [y4 aB (by decide), x4]
  · rw [y3.rc, hrc10, f4 sDp (by decide) hne1, hs4, DS.rew_rc_ne _ hne1, DS.set_rc, g2, s1Dp]
  · rw [y3.rc, hrc10, f2, s4Dn]
  · intro m h1 h2 h3
    rw [y3.rc, hrc10, f4 m h2 h3, hs4, DS.rew_rc_ne _ h3, DS.set_rc, g4 m h1 h3, hs1, DS.set_rc, DS.rew_rc_ne _ h3]
  · rw [y3.rc, hrc10, f3, s4F]; omega
  · rw [y3.ram, hram10, f5, s4ram]
  · rw [y3.ip, hb10]; simp only [DS.set_ip]; rw [f6, hs4, DS.rew_ip, DS.set_ip, g6, hs1, DS.set_ip, DS.rew_ip]
  · rw [y3.out, hb10]; simp only [DS.set_out]; rw [f7, hs4, DS.rew_out, DS.set_out, g7, hs1, DS.set_out, DS.rew_out]
  · rw [y3.kin, hb10]; simp only [DS.set_kin]; rw [f8, hs4, DS.rew_kin, DS.set_kin, g8, hs1, DS.set_kin, DS.rew_kin]
  · rw [y3.kout, hb10]; simp only [DS.set_kout]
    rw [f9, hs4, DS.rew_kout, DS.set_kout, g9, hs1, DS.set_kout, DS.rew_kout]
  · rw [y3.kc, hb10]; simp only [DS.set_kc]; rw [f10, hs4, DS.rew_kc, DS.set_kc, g10, hs1, DS.set_kc, DS.rew_kc]
  · intro y hy
    rw [y4 y (fun h => hy (hxT y h))]
    have hy' : y ∉ [vN, vH, vI, vT, vR, aHp, aHn, aM, aA, aL, aB, vLo, vLen, xP1, xP2, xP3, xX, xY, xR, xQ, xC] := hy
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy'
    rw [hb10]
    simp only [DS.set_env_ne _ _ hy'.2.2.2.2.2.2.1, DS.set_env_ne _ _ hy'.2.2.2.2.2.2.2.1,
      DS.set_env_ne _ _ hy'.2.2.2.2.2.2.2.2.1, DS.set_env_ne _ _ hy'.2.2.2.2.2.2.2.2.2.1,
      DS.set_env_ne _ _ hy'.2.2.2.2.2.2.2.2.2.2.1]
    exact kpre y hy
  · exact y5
  · have g3' : b2.rc sF = N := by rw [g3, s1F]; omega
    simp only [DS.set_rc, g3'] at hn4
    omega

end NearQuarticWires.Reconstruct
