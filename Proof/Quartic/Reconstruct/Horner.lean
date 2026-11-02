import Proof.Quartic.Reconstruct.BoxArith
import Proof.Gates.Cells.Kit

/-!
# Horner's scheme in the cell language

Paper: `lem:certify`(d), paper/paper.tex (the digit value `K(δ^{(j)})` of a digit vector under the
rates).

`hornerS` reads the digits `d_0, d_1, …, d_N` from a record store (from its cursor on) and the rates
`a_0, …, a_{N-1}` from another store (from its cursor on), and computes `hornerN a d N` (`BoxArith.hornerN`):
`H := d_0`, then `H := a_i H + d_{i+1}` (`hornerS_spec`).
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearCubicGates.Close.Cells

variable {C : Ctx}

/-- The value `H`. -/
def vH : Fin VV := ⟨20, by decide⟩
/-- The counter `i`. -/
def vI : Fin VV := ⟨21, by decide⟩
/-- The bound `N`. -/
def vN : Fin VV := ⟨22, by decide⟩
/-- Scratch: a product. -/
def vT : Fin VV := ⟨23, by decide⟩
/-- Scratch: a read record. -/
def vR : Fin VV := ⟨24, by decide⟩

/-- Horner's scheme over the digits of store `sD` and the rates of store `sF`, `N` (in `vN`) steps. -/
def hornerS (sD sF : Fin MM) : St VV MM :=
  .seq (.op (.rdM sD vH)) (.seq (.op (.zero vI)) (.loop (.lt vI vN)
    (.seq (.op (.rdM sF vR)) (.seq (.op (.mul vH vR vT)) (.seq (.op (.rdM sD vR)) (.seq (.op (.copy vH vT))
      (.seq (.op (.add vH vR)) (.op (.inc vI)))))))))

/-- The variables written by `hornerS`. -/
def hornerT : List (Fin VV) := [vH, vI, vT, vR]

/-- The digits read from position `p` of a store. -/
def storeDig (D : List ℕ) (p : ℕ) (i : ℕ) : ℕ := D.getD (p + i) 0

theorem DS.adv_env {V M : ℕ} (a : DS V M) (m : Fin M) : (a.adv m).env = a.env := rfl
theorem DS.adv_ram {V M : ℕ} (a : DS V M) (m : Fin M) : (a.adv m).ram = a.ram := rfl
theorem DS.adv_rc_self {V M : ℕ} (a : DS V M) (m : Fin M) : (a.adv m).rc m = a.rc m + 1 := by
  simp [DS.adv]
theorem DS.adv_rc_ne {V M : ℕ} (a : DS V M) {m m' : Fin M} (h : m' ≠ m) : (a.adv m).rc m' = a.rc m' := by
  simp [DS.adv, Function.update_of_ne h]

/-- **Horner's scheme.** From cursors `p` (digits) and `f` (rates), with `N` in `vN`, `hornerS` leaves
`hornerN (a) (d) N` in `vH`, where `a_i` and `d_i` are the records at `f + i` and `p + i`; the cursors advance by
`N` and `N + 1`. -/
theorem hornerS_spec (sD sF : Fin MM) (hsDF : sD ≠ sF) (a : DS VV MM) (hc : Cst a) (N : ℕ) (hN : a.env vN = N)
    (hD : a.rc sD + N < (a.ram sD).length) (hF : a.rc sF + N ≤ (a.ram sF).length)
    (hfit : ∀ i < N, (a.ram sF).getD (a.rc sF + i) 0 *
        hornerN (storeDig (a.ram sF) (a.rc sF)) (storeDig (a.ram sD) (a.rc sD)) i +
        storeDig (a.ram sD) (a.rc sD) (i + 1) < 2 ^ C.Wd)
    (hNW : N < 2 ^ C.Wd) :
    Hs C (hornerS sD sF) a (N * 13 + 6)
      (fun b => b.env vH = hornerN (storeDig (a.ram sF) (a.rc sF)) (storeDig (a.ram sD) (a.rc sD)) N ∧
        b.rc sD = a.rc sD + N + 1 ∧ b.rc sF = a.rc sF + N ∧ (∀ m, m ≠ sD → m ≠ sF → b.rc m = a.rc m) ∧
        b.ram = a.ram ∧ b.ip = a.ip ∧ b.out = a.out ∧ b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧
        Fr a b hornerT ∧ Cst b) := by
  set Fs := storeDig (a.ram sF) (a.rc sF) with hFs
  set Ds := storeDig (a.ram sD) (a.rc sD) with hDs
  have hcT : vZ ∉ hornerT ∧ v1 ∉ hornerT ∧ v2 ∉ hornerT := by decide
  -- the invariant after `i` passes
  let I : ℕ → DS VV MM → Prop := fun i b => b.env vH = hornerN Fs Ds i ∧ b.env vI = i ∧ b.env vN = N ∧
    b.rc sD = a.rc sD + i + 1 ∧ b.rc sF = a.rc sF + i ∧ (∀ m, m ≠ sD → m ≠ sF → b.rc m = a.rc m) ∧
    b.ram = a.ram ∧ b.ip = a.ip ∧ b.out = a.out ∧ b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧
    Fr a b hornerT
  have hvN : ∀ (b : DS VV MM), Fr a b hornerT → b.env vN = N := fun b h => by rw [h vN (by decide), hN]
  have loop : ∀ b, I 0 b → Hs C (.loop (.lt vI vN)
      (.seq (.op (.rdM sF vR)) (.seq (.op (.mul vH vR vT)) (.seq (.op (.rdM sD vR)) (.seq (.op (.copy vH vT))
        (.seq (.op (.add vH vR)) (.op (.inc vI)))))))) b (N * (11 + 2) + 2) (I N) := by
    refine Hs.loopN (c := .lt vI vN) (show vI ≠ vN by decide) I N 11 ?_ ?_
    · intro i hi b ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩
      refine ⟨by simp [Cnd.eval, h2, h3, hi], ?_⟩
      have hrF : b.rc sF < (b.ram sF).length := by rw [h5, h7]; omega
      refine Hs.seq (t1 := 1) (t2 := 9) (hs_rdM C sF vR b hrF) (fun b1 hb1 => ?_)
      subst hb1
      have r1 : ((b.set vR ((b.ram sF).getD (b.rc sF) 0)).adv sF).env vR = Fs i := by
        simp only [DS.adv_env, DS.set_env_self, h5, h7, hFs, storeDig]
      have r1H : ((b.set vR ((b.ram sF).getD (b.rc sF) 0)).adv sF).env vH = hornerN Fs Ds i := by
        simp only [DS.adv_env]; vsimp [h1]
      have hmul : ((b.set vR ((b.ram sF).getD (b.rc sF) 0)).adv sF).env vH *
          ((b.set vR ((b.ram sF).getD (b.rc sF) 0)).adv sF).env vR < 2 ^ C.Wd := by
        rw [r1H, r1]
        have := hfit i hi
        have e : Fs i = (a.ram sF).getD (a.rc sF + i) 0 := rfl
        rw [e, mul_comm]
        omega
      refine Hs.seq (t1 := 1) (t2 := 7) (hs_mul C vH vR vT _ (by decide) (by decide) (by decide) hmul)
        (fun b2 hb2 => ?_)
      subst hb2
      set b1 := (b.set vR ((b.ram sF).getD (b.rc sF) 0)).adv sF with hb1def
      have hrD : (b1.set vT (b1.env vH * b1.env vR)).rc sD < ((b1.set vT (b1.env vH * b1.env vR)).ram sD).length := by
        simp only [DS.set, hb1def, DS.adv, Function.update_of_ne hsDF, h4, h7]
        omega
      refine Hs.seq (t1 := 1) (t2 := 5) (hs_rdM C sD vR _ hrD) (fun b3 hb3 => ?_)
      subst hb3
      refine Hs.seq (t1 := 1) (t2 := 3) (hs_copy C vH vT _ (by decide)) (fun b4 hb4 => ?_)
      subst hb4
      have hdig : (b1.set vT (b1.env vH * b1.env vR)).ram sD = a.ram sD := by
        simp only [DS.set, hb1def, DS.adv, h7]
      have hcur : (b1.set vT (b1.env vH * b1.env vR)).rc sD = a.rc sD + (i + 1) := by
        simp only [DS.set, hb1def, DS.adv, Function.update_of_ne hsDF, h4]
        omega
      have hvR : ((b1.set vT (b1.env vH * b1.env vR)).set vR
          (((b1.set vT (b1.env vH * b1.env vR)).ram sD).getD ((b1.set vT (b1.env vH * b1.env vR)).rc sD) 0)).env vR
          = Ds (i + 1) := by
        rw [DS.set_env_self, hdig, hcur]; rfl
      set b3 := ((b1.set vT (b1.env vH * b1.env vR)).set vR
          (((b1.set vT (b1.env vH * b1.env vR)).ram sD).getD ((b1.set vT (b1.env vH * b1.env vR)).rc sD) 0)).adv sD
        with hb3def
      have b3R : b3.env vR = Ds (i + 1) := by rw [hb3def, DS.adv_env, hvR]
      have b3T : b3.env vT = hornerN Fs Ds i * Fs i := by
        rw [hb3def, DS.adv_env, DS.set_env_ne _ _ (by decide), DS.set_env_self, r1H, r1]
      have b3I : b3.env vI = i := by
        rw [hb3def, DS.adv_env, DS.set_env_ne _ _ (by decide), DS.set_env_ne _ _ (by decide), hb1def,
          DS.adv_env, DS.set_env_ne _ _ (by decide), h2]
      have hadd : (b3.set vH (b3.env vT)).env vH + (b3.set vH (b3.env vT)).env vR < 2 ^ C.Wd := by
        have := hfit i hi
        have e : Fs i = (a.ram sF).getD (a.rc sF + i) 0 := rfl
        vsimp [b3T, b3R]
        rw [e, mul_comm]
        exact this
      refine Hs.seq (t1 := 1) (t2 := 1) (hs_add C vH vR _ (by decide) hadd) (fun b5 hb5 => ?_)
      subst hb5
      refine Hs.mono (hs_inc C vI _ (by vsimp [b3I]; omega)) le_rfl ?_
      rintro b6 rfl
      have hfr3 : Fr a b3 hornerT := by
        intro y hy
        have hy' : y ∉ [vH, vI, vT, vR] := hy
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy'
        rw [hb3def, DS.adv_env]
        vsimp [hb1def, DS.adv_env, Function.update_of_ne hy'.2.2.2, Function.update_of_ne hy'.2.2.1]
        exact h13 y hy
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · vsimp [b3T, b3R]
        show hornerN Fs Ds i * Fs i + Ds (i + 1) = Fs i * hornerN Fs Ds i + Ds (i + 1)
        ring
      · vsimp [b3I]
      · vsimp [hfr3 vN (by decide), hN]
      · rw [DS.set_rc, DS.set_rc, DS.set_rc, hb3def, DS.adv_rc_self, DS.set_rc, hcur]
      · rw [DS.set_rc, DS.set_rc, DS.set_rc, hb3def, DS.adv_rc_ne _ (Ne.symm hsDF), DS.set_rc, DS.set_rc, hb1def,
          DS.adv_rc_self, DS.set_rc, h5]
        omega
      · intro m hm1 hm2
        rw [DS.set_rc, DS.set_rc, DS.set_rc, hb3def, DS.adv_rc_ne _ hm1, DS.set_rc, DS.set_rc, hb1def,
          DS.adv_rc_ne _ hm2, DS.set_rc]
        exact h6 m hm1 hm2
      · rw [DS.set_ram, DS.set_ram, DS.set_ram, hb3def, DS.adv_ram, DS.set_ram, DS.set_ram, hb1def, DS.adv_ram,
          DS.set_ram, h7]
      · simp only [DS.set_ip, hb3def, hb1def, DS.adv, h8]
      · simp only [DS.set_out, hb3def, hb1def, DS.adv, h9]
      · simp only [DS.set_kin, hb3def, hb1def, DS.adv, h10]
      · simp only [DS.set_kout, hb3def, hb1def, DS.adv, h11]
      · simp only [DS.set_kc, hb3def, hb1def, DS.adv, h12]
      · exact Fr.trans hfr3 (Fr.trans (Fr.set _ _ (show vH ∈ hornerT by decide))
          (Fr.trans (Fr.set _ _ (show vH ∈ hornerT by decide)) (Fr.set _ _ (show vI ∈ hornerT by decide))))
    · intro b ⟨_, h2, h3, _⟩
      simp [Cnd.eval, h2, h3]
  -- the whole
  have hrD0 : a.rc sD < (a.ram sD).length := by omega
  refine Hx.hs (Hs.then (hs_rdM C sD vH a hrD0) (fun b0 hb0 n0 hn0 => ?_))
  subst hb0
  refine Hs.then (hs_zero C vI _) (fun b1 hb1 n1 hn1 => ?_)
  subst hb1
  refine Hs.last (loop _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩) ?_
  · vsimp [DS.adv_env]; rfl
  · vsimp []
  · vsimp [DS.adv_env, hN]
  · simp [DS.set, DS.adv]
  · simp [DS.set, DS.adv, Function.update_of_ne (Ne.symm hsDF)]
  · intro m hm1 _; simp [DS.set, DS.adv, Function.update_of_ne hm1]
  · simp [DS.set, DS.adv]
  · simp [DS.set, DS.adv]
  · simp [DS.set, DS.adv]
  · simp [DS.set, DS.adv]
  · simp [DS.set, DS.adv]
  · simp [DS.set, DS.adv]
  · exact Fr.trans (fun y hy => by simp only [DS.adv_env]; exact DS.set_env_ne _ _ (fun h => hy (h ▸ by decide)))
      (Fr.set _ _ (by decide))
  · rintro b ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13⟩ n hn
    exact ⟨⟨g1, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, Cst.of_fr hc g13 hcT⟩, by omega⟩

end NearQuarticWires.Reconstruct
