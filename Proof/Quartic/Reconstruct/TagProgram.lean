import Proof.Quartic.Reconstruct.PointsProgram
import Proof.Quartic.Reconstruct.ZeroIndex

/-!
# The tag of a system in the cell language

Paper: Step 3 of `sec:algorithm`, paper/paper.tex.

The tag of a listed system (`Phases.systemTag`) is its coefficient `(±1)κ_σ = ±2` in `Ψ̃(π)` (`κ_σ = 2` when
`κ_σ ≠ 0`) and the position of the point `0` among its points (`ZeroIndex.idxOf_zero_box`). `zeroIndexS` computes
this position (`zeroIndexS_spec`); `tagS d` writes `intWord (±2) ++ natWord idx₀` at depth `d` (`tagS_spec`).
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells

variable {C : Ctx}

/-- The part of the weights, `1` for the positive part and `0` for the negative part. -/
def gS : Fin VV := ⟨59, by decide⟩
/-- Scratch: a flag. -/
def gF : Fin VV := ⟨60, by decide⟩
/-- Scratch: a sum. -/
def gU : Fin VV := ⟨61, by decide⟩
/-- Scratch: a product. -/
def gV : Fin VV := ⟨62, by decide⟩

/-- The position of the point `0` in a box with coordinate intervals `(lo'_j, len_j, B_j)`. -/
def zeroIndex (lo0 len0 B0 lo1 len1 B1 : ℕ) : ℕ :=
  if lo0 ≤ B0 ∧ B0 < lo0 + len0 ∧ lo1 ≤ B1 ∧ B1 < lo1 + len1 then (B0 - lo0) * len1 + (B1 - lo1) else len0 * len1

/-- `t3 := len_1 len_2` (the number of points). -/
def allS : St VV MM := .op (.mul pLen0 pLen1 t3)

/-- `t3 := (B_1 - lo'_1) len_2 + (B_2 - lo'_2)`. -/
def idxS : St VV MM :=
  .seq (.op (.copy t3 pB0)) (.seq (.op (.sub t3 pLo0)) (.seq (.op (.mul t3 pLen1 gV)) (.seq (.op (.copy t3 pB1))
    (.seq (.op (.sub t3 pLo1)) (.op (.add t3 gV))))))

/-- The position of the point `0`, into `t3`. -/
def zeroIndexS : St VV MM :=
  .ite (.lt pB0 pLo0) allS
    (.seq (.op (.copy gU pLo0)) (.seq (.op (.add gU pLen0)) (.ite (.lt pB0 gU)
      (.ite (.lt pB1 pLo1) allS (.seq (.op (.copy gU pLo1)) (.seq (.op (.add gU pLen1))
        (.ite (.lt pB1 gU) idxS allS))))
      allS)))

/-- The variables written by `zeroIndexS`. -/
def zeroT : List (Fin VV) := [t3, gU, gV]

/-- The facts kept by the position program: the six inputs, the non-variable state and the constants. -/
structure ZeroKeep (a b : DS VV MM) : Prop where
  same : Same a b
  fr : Fr a b zeroT
  cst : Cst b

theorem zeroT_ne : ∀ y ∈ zeroT, vZ ≠ y ∧ v1 ≠ y ∧ v2 ≠ y := by decide

theorem zeroKeep_set {a b : DS VV MM} (h : ZeroKeep a b) {x : Fin VV} (hx : x ∈ zeroT) (v : ℕ) :
    ZeroKeep a (b.set x v) :=
  ⟨Same.trans h.same (Same.set b x v), Fr.trans h.fr (Fr.set b v hx),
    ⟨by rw [DS.set_env_ne _ _ (zeroT_ne x hx).1]; exact h.cst.z,
      by rw [DS.set_env_ne _ _ (zeroT_ne x hx).2.1]; exact h.cst.one,
      by rw [DS.set_env_ne _ _ (zeroT_ne x hx).2.2]; exact h.cst.two⟩⟩

theorem zeroIndexS_spec (a : DS VV MM) (hc : Cst a)
    (hbig : (a.env pLo0 + a.env pLen0 + a.env pB0 + a.env pLo1 + a.env pLen1 + a.env pB1 + 1) ^ 2 < 2 ^ C.Wd) :
    Hs C zeroIndexS a 30 (fun b => b.env t3 = zeroIndex (a.env pLo0) (a.env pLen0) (a.env pB0) (a.env pLo1)
      (a.env pLen1) (a.env pB1) ∧ ZeroKeep a b) := by
  obtain ⟨lo0, hlo0⟩ : ∃ v, a.env pLo0 = v := ⟨_, rfl⟩
  obtain ⟨len0, hlen0⟩ : ∃ v, a.env pLen0 = v := ⟨_, rfl⟩
  obtain ⟨B0, hB0⟩ : ∃ v, a.env pB0 = v := ⟨_, rfl⟩
  obtain ⟨lo1, hlo1⟩ : ∃ v, a.env pLo1 = v := ⟨_, rfl⟩
  obtain ⟨len1, hlen1⟩ : ∃ v, a.env pLen1 = v := ⟨_, rfl⟩
  obtain ⟨B1, hB1⟩ : ∃ v, a.env pB1 = v := ⟨_, rfl⟩
  rw [hlo0, hlen0, hB0, hlo1, hlen1, hB1] at hbig ⊢
  obtain ⟨S, hS⟩ : ∃ v, lo0 + len0 + B0 + lo1 + len1 + B1 + 1 = v := ⟨_, rfl⟩
  rw [hS] at hbig
  have hsq : S ≤ S ^ 2 := Nat.le_self_pow (by norm_num) _
  have hlt : ∀ x ≤ S ^ 2, x < 2 ^ C.Wd := fun x hx => by omega
  have k0 : ZeroKeep a a := ⟨Same.refl a, Fr.refl a _, hc⟩
  -- the number of points, from any state that keeps the inputs
  have hall : ∀ b, ZeroKeep a b → b.env pLen0 = len0 → b.env pLen1 = len1 →
      Hs C allS b 1 (fun c => c.env t3 = len0 * len1 ∧ ZeroKeep a c) := by
    intro b hb e0 e1
    have ml : len0 * len1 ≤ S ^ 2 := by rw [pow_two]; exact Nat.mul_le_mul (by omega) (by omega)
    refine Hs.mono (hs_mul C pLen0 pLen1 t3 b (by decide) (by decide) (by decide)
      (by rw [e0, e1]; exact hlt _ ml)) le_rfl ?_
    rintro c rfl
    exact ⟨by vsimp [hlo0, hlen0, hB0, hlo1, hlen1, hB1, e0, e1], zeroKeep_set hb (by decide) _⟩
  have hdis : ∀ y ∈ [pLo0, pLen0, pB0, pLo1, pLen1, pB1], y ∉ zeroT := by decide
  have kv : ∀ b, ZeroKeep a b → ∀ y ∈ [pLo0, pLen0, pB0, pLo1, pLen1, pB1], b.env y = a.env y := by
    intro b hb y hy
    exact hb.fr y (hdis y hy)
  have vals := And.intro hlo0 (And.intro hlen0 (And.intro hB0 (And.intro hlo1 (And.intro hlen1 hB1))))
  refine Hs.ite (c := .lt pB0 pLo0) (show pB0 ≠ pLo0 by decide) (fun he => ?_) (fun he => ?_)
  · have h : B0 < lo0 := by simpa [Cnd.eval, hB0, hlo0] using he
    refine (hall a k0 hlen0 hlen1).mono (by norm_num) (fun c ⟨c1, c2⟩ => ⟨?_, c2⟩)
    rw [c1, zeroIndex, if_neg (by omega)]
  · have h : lo0 ≤ B0 := by simpa [Cnd.eval, hB0, hlo0] using he
    refine Hx.hs (Hs.then (hs_copy C gU pLo0 a (by decide)) (fun b0 hb0 n0 hn0 => ?_))
    subst hb0
    refine Hs.then (hs_add C gU pLen0 _ (by decide) (by vsimp [hlo0, hlen0, hB0, hlo1, hlen1, hB1]; exact hlt _ (by omega)))
      (fun b1 hb1 n1 hn1 => ?_)
    subst hb1
    have kb1 : ZeroKeep a ((a.set gU (a.env pLo0)).set gU ((a.set gU (a.env pLo0)).env gU +
        (a.set gU (a.env pLo0)).env pLen0)) := zeroKeep_set (zeroKeep_set k0 (by decide) _) (by decide) _
    have kvb1 := kv _ kb1
    have gLo1 := (kvb1 pLo1 (by simp)).trans hlo1
    have gLen1 := (kvb1 pLen1 (by simp)).trans hlen1
    have gLen0 := (kvb1 pLen0 (by simp)).trans hlen0
    have gB1 := (kvb1 pB1 (by simp)).trans hB1
    refine Hs.last (Hs.ite (c := .lt pB0 gU) (t := 21) (show pB0 ≠ gU by decide) (fun he1 => ?_) (fun he1 => ?_))
      (fun c hc' n hn => ⟨hc', by omega⟩)
    · have h1 : B0 < lo0 + len0 := by
        simp only [Cnd.eval, decide_eq_true_eq] at he1
        vsimp [hlo0, hlen0, hB0, hlo1, hlen1, hB1] at he1
        exact he1
      refine Hs.ite (c := .lt pB1 pLo1) (t := 20) (show pB1 ≠ pLo1 by decide) (fun he2 => ?_) (fun he2 => ?_)
      · have h2 : B1 < lo1 := by
          simp only [Cnd.eval, decide_eq_true_eq] at he2
          rwa [gB1, gLo1] at he2
        refine (hall _ kb1 gLen0 gLen1).mono (by norm_num)
          (fun c ⟨c1, c2⟩ => ⟨?_, c2⟩)
        rw [c1, zeroIndex, if_neg (by omega)]
      · have h2 : lo1 ≤ B1 := by
          simp only [Cnd.eval, decide_eq_false_iff_not, not_lt] at he2
          rwa [gB1, gLo1] at he2
        refine Hx.hs (Hs.then (hs_copy C gU pLo1 _ (by decide)) (fun b2 hb2 n2 hn2 => ?_))
        subst hb2
        refine Hs.then (hs_add C gU pLen1 _ (by decide) (by vsimp [hlo0, hlen0, hB0, hlo1, hlen1, hB1, gLo1, gLen1]; exact hlt _ (by omega)))
          (fun b3 hb3 n3 hn3 => ?_)
        have kb3 : ZeroKeep a b3 := by
          rw [hb3]; exact zeroKeep_set (zeroKeep_set kb1 (by decide) _) (by decide) _
        have kvb3 := kv _ kb3
        have fB0 := (kvb3 pB0 (by simp)).trans hB0
        have fLo0 := (kvb3 pLo0 (by simp)).trans hlo0
        have fLen1 := (kvb3 pLen1 (by simp)).trans hlen1
        have fB1 := (kvb3 pB1 (by simp)).trans hB1
        have fLo1 := (kvb3 pLo1 (by simp)).trans hlo1
        have eU : b3.env gU = lo1 + len1 := by
          rw [hb3]; vsimp [hlo0, hlen0, hB0, hlo1, hlen1, hB1, gLo1, gLen1]
        refine Hs.last (Hs.ite (c := .lt pB1 gU) (t := 11) (show pB1 ≠ gU by decide) (fun he3 => ?_) (fun he3 => ?_))
          (fun c hc' n hn => ⟨hc', by omega⟩)
        · have h3 : B1 < lo1 + len1 := by
            simp only [Cnd.eval, decide_eq_true_eq] at he3
            rwa [fB1, eU] at he3
          refine Hx.hs (Hs.then (hs_copy C t3 pB0 b3 (by decide)) (fun c0 hc0 m0 hm0 => ?_))
          subst hc0
          refine Hs.then (hs_sub C t3 pLo0 _ (by decide) (by vsimp [hlo0, hlen0, hB0, hlo1, hlen1, hB1, fB0, fLo0]; omega)) (fun c1 hc1 m1 hm1 => ?_)
          subst hc1
          have mb1 : (B0 - lo0) * len1 ≤ S ^ 2 := by
            rw [pow_two]; exact Nat.mul_le_mul (by omega) (by omega)
          have mb2 : (B0 - lo0) * len1 + (B1 - lo1) ≤ S ^ 2 := by
            have e1 : (B0 - lo0) * len1 ≤ B0 * len1 := Nat.mul_le_mul_right _ (by omega)
            have e2 : B0 * len1 + B1 ≤ (B0 + B1) * (len1 + 1) := by nlinarith
            have e3 : (B0 + B1) * (len1 + 1) ≤ S * S := Nat.mul_le_mul (by omega) (by omega)
            rw [pow_two]; omega
          refine Hs.then (hs_mul C t3 pLen1 gV _ (by decide) (by decide) (by decide) (by
            vsimp [hlo0, hlen0, hB0, hlo1, hlen1, hB1, fB0, fLo0, fLen1]
            exact hlt _ mb1)) (fun c2 hc2 m2 hm2 => ?_)
          subst hc2
          refine Hs.then (hs_copy C t3 pB1 _ (by decide)) (fun c3 hc3 m3 hm3 => ?_)
          subst hc3
          refine Hs.then (hs_sub C t3 pLo1 _ (by decide) (by vsimp [hlo0, hlen0, hB0, hlo1, hlen1, hB1, fB1, fLo1]; omega)) (fun c4 hc4 m4 hm4 => ?_)
          subst hc4
          refine Hs.last (hs_add C t3 gV _ (by decide) (by
            vsimp [hlo0, hlen0, hB0, hlo1, hlen1, hB1, fB0, fLo0, fLen1, fB1, fLo1]
            exact hlt _ (by omega))) (fun c5 hc5 m5 hm5 => ?_)
          subst hc5
          refine ⟨⟨?_, zeroKeep_set (zeroKeep_set (zeroKeep_set (zeroKeep_set (zeroKeep_set (zeroKeep_set kb3
            (by decide) _) (by decide) _) (by decide) _) (by decide) _) (by decide) _) (by decide) _⟩, by omega⟩
          rw [zeroIndex, if_pos ⟨h, h1, h2, h3⟩]
          vsimp [hlo0, hlen0, hB0, hlo1, hlen1, hB1, fB0, fLo0, fLen1, fB1, fLo1]
          ring
        · have h3 : ¬ B1 < lo1 + len1 := by
            simp only [Cnd.eval, decide_eq_false_iff_not] at he3
            rwa [fB1, eU] at he3
          refine (hall _ kb3 ((kvb3 pLen0 (by simp)).trans hlen0) fLen1).mono (by norm_num)
            (fun c ⟨c1, c2⟩ => ⟨?_, c2⟩)
          rw [c1, zeroIndex, if_neg (by omega)]
    · have h1 : ¬ B0 < lo0 + len0 := by
        simp only [Cnd.eval, decide_eq_false_iff_not] at he1
        vsimp [hlo0, hlen0, hB0, hlo1, hlen1, hB1] at he1
        omega
      refine (hall _ kb1 gLen0 gLen1).mono (by norm_num)
        (fun c ⟨c1, c2⟩ => ⟨?_, c2⟩)
      rw [c1, zeroIndex, if_neg (by omega)]

/-! ## The tag -/

/-- Write `intWord (±2) ++ natWord idx₀` at depth `d` (`+2` when `gS = 1`). -/
def tagS (d : ℕ) : St VV MM :=
  .seq (.ite (.eq gS v1) (.op (.zero t3)) (.op (.copy t3 v1))) (.seq (emitNatD d) (.seq (.op (.copy t3 v2))
    (.seq (emitNatD d) (.seq zeroIndexS (emitNatD d)))))

/-- The variables written by `tagS`. -/
def tagT : List (Fin VV) := [t3, gU, gV, t5, t6, t7, t8, t9, vJ]

/-- The coefficient `±2` of the positive (`true`) or negative part. -/
def coefOf (s : Bool) : ℤ := if s then 2 else -2

theorem add_two_lt_two_pow : ∀ k : ℕ, 3 ≤ k → k + 2 < 2 ^ k
  | 0, h => absurd h (by norm_num)
  | 1, h => absurd h (by norm_num)
  | 2, h => absurd h (by norm_num)
  | 3, _ => by norm_num
  | k + 4, _ => by
    have := add_two_lt_two_pow (k + 3) (by omega)
    rw [pow_succ]
    omega

theorem natBitLength_le_of_lt_two_pow {v k : ℕ} (hv : v < 2 ^ k) (hk : 1 ≤ k) : natBitLength v ≤ k := by
  unfold natBitLength
  rcases Nat.eq_zero_or_pos v with rfl | hpos
  · simp; omega
  · have := Nat.log_lt_of_lt_pow (b := 2) (by omega) hv
    omega

theorem zeroIndex_le (lo0 len0 B0 lo1 len1 B1 : ℕ) :
    zeroIndex lo0 len0 B0 lo1 len1 B1 ≤ (lo0 + len0 + B0 + lo1 + len1 + B1 + 1) ^ 2 := by
  set S := lo0 + len0 + B0 + lo1 + len1 + B1 + 1 with hS
  unfold zeroIndex
  split_ifs
  · have e1 : (B0 - lo0) * len1 ≤ B0 * len1 := Nat.mul_le_mul_right _ (by omega)
    have e2 : B0 * len1 + B1 ≤ (B0 + B1) * (len1 + 1) := by nlinarith
    have e3 : (B0 + B1) * (len1 + 1) ≤ S * S := Nat.mul_le_mul (by omega) (by omega)
    rw [pow_two]; omega
  · rw [pow_two]; exact Nat.mul_le_mul (by omega) (by omega)

theorem tagS_spec (d : ℕ) (a : DS VV MM) (hc : Cst a) (hW : 3 ≤ C.Wd) (s : Bool)
    (hs : a.env gS = if s then 1 else 0)
    (hbig : (a.env pLo0 + a.env pLen0 + a.env pB0 + a.env pLo1 + a.env pLen1 + a.env pB1 + 1) ^ 2 < 2 ^ C.Wd) :
    Hs C (tagS d) a (3 * emitNatDCost d C.Wd + 50)
      (fun b => Wrote a b (marksD d (NearCubicGates.Close.Interfaces.intWord (coefOf s) ++
        natWord (zeroIndex (a.env pLo0) (a.env pLen0) (a.env pB0) (a.env pLo1) (a.env pLen1) (a.env pB1))))
        tagT ∧ Cst b) := by
  have h2W := add_two_lt_two_pow C.Wd hW
  have hWd : 2 ≤ C.Wd := by omega
  have hnb : ∀ v, v < 2 ^ C.Wd → natBitLength v + 2 < 2 ^ C.Wd := fun v hv =>
    lt_of_le_of_lt (Nat.add_le_add_right (natBitLength_le_of_lt_two_pow hv (by omega)) 2) h2W
  have hcost : ∀ v, v < 2 ^ C.Wd → emitNatDCost d (natBitLength v) ≤ emitNatDCost d C.Wd := by
    intro v hv
    unfold emitNatDCost
    exact Nat.mul_le_mul_left _ (by have := natBitLength_le_of_lt_two_pow hv (by omega); omega)
  have hnT : ∀ y ∈ emitNatDT, y ∈ tagT := by decide
  have hzT : ∀ y ∈ zeroT, y ∈ tagT := by decide
  have h3 : t3 ∈ tagT := by decide
  have hcT : vZ ∉ tagT ∧ v1 ∉ tagT ∧ v2 ∉ tagT := by decide
  have hin : ∀ y ∈ [pLo0, pLen0, pB0, pLo1, pLen1, pB1], y ∉ tagT := by decide
  -- the sign word
  have hsign : Hs C (.ite (.eq gS v1) (.op (.zero t3)) (.op (.copy t3 v1))) a 2
      (fun b => b = a.set t3 (if s then 0 else 1)) := by
    refine Hs.ite (c := .eq gS v1) (show gS ≠ v1 by decide) (fun he => ?_) (fun he => ?_)
    · have hs1 : s = true := by
        cases s
        · simp [Cnd.eval, hs, hc.one] at he
        · rfl
      subst hs1
      exact Hs.mono (hs_zero C t3 a) (by norm_num) (fun b hb => by rw [hb]; simp)
    · have hs1 : s = false := by
        cases s
        · rfl
        · simp [Cnd.eval, hs, hc.one] at he
      subst hs1
      exact Hs.mono (hs_copy C t3 v1 a (by decide)) (by norm_num) (fun b hb => by rw [hb, hc.one]; simp)
  refine Hx.hs (Hs.then hsign (fun b0 hb0 n0 hn0 => ?_))
  subst hb0
  have c0 : Cst (a.set t3 (if s then 0 else 1)) := ⟨by vsimp [hc.z], by vsimp [hc.one], by vsimp [hc.two]⟩
  have e0 : (a.set t3 (if s then 0 else 1)).env t3 = if s then 0 else 1 := by vsimp []
  have hv0 : (if s then 0 else 1 : ℕ) < 2 ^ C.Wd := by split <;> omega
  refine Hs.then (emitNatD_spec d _ c0 hWd (by rw [e0]; exact hnb _ hv0)) (fun b1 ⟨w1, c1⟩ n1 hn1 => ?_)
  rw [e0] at w1 hn1
  refine Hs.then (hs_copy C t3 v2 b1 (by decide)) (fun b2 hb2 n2 hn2 => ?_)
  subst hb2
  have c2 : Cst (b1.set t3 (b1.env v2)) := ⟨by vsimp [c1.z], by vsimp [c1.one], by vsimp [c1.two]⟩
  have e2 : (b1.set t3 (b1.env v2)).env t3 = 2 := by vsimp [c1.two]
  refine Hs.then (emitNatD_spec d _ c2 hWd (by rw [e2]; exact hnb _ (by omega))) (fun b3 ⟨w3, c3⟩ n3 hn3 => ?_)
  rw [e2] at w3 hn3
  -- the inputs are kept
  have w03 : Wrote a b3 (marksD d (natWord (if s then 0 else 1)) ++ marksD d (natWord 2)) tagT :=
    ((((Wrote.refl a tagT).set _ h3).trans (w1.weaken hnT)).trans (((Wrote.refl b1 tagT).set _ h3).trans
      (w3.weaken hnT)))
  have kv : ∀ y ∈ [pLo0, pLen0, pB0, pLo1, pLen1, pB1], b3.env y = a.env y := fun y hy => w03.fr y (hin y hy)
  have hbig3 : (b3.env pLo0 + b3.env pLen0 + b3.env pB0 + b3.env pLo1 + b3.env pLen1 + b3.env pB1 + 1) ^ 2 <
      2 ^ C.Wd := by
    rw [kv pLo0 (by simp), kv pLen0 (by simp), kv pB0 (by simp), kv pLo1 (by simp), kv pLen1 (by simp),
      kv pB1 (by simp)]
    exact hbig
  refine Hs.then (zeroIndexS_spec b3 c3 hbig3) (fun b4 ⟨e4, k4⟩ n4 hn4 => ?_)
  rw [kv pLo0 (by simp), kv pLen0 (by simp), kv pB0 (by simp), kv pLo1 (by simp), kv pLen1 (by simp),
    kv pB1 (by simp)] at e4
  have hz : zeroIndex (a.env pLo0) (a.env pLen0) (a.env pB0) (a.env pLo1) (a.env pLen1) (a.env pB1) < 2 ^ C.Wd :=
    lt_of_le_of_lt (zeroIndex_le _ _ _ _ _ _) hbig
  refine Hs.last (emitNatD_spec d _ k4.cst hWd (by rw [e4]; exact hnb _ hz)) (fun b5 ⟨w5, c5⟩ n5 hn5 => ?_)
  rw [e4] at w5 hn5
  refine ⟨⟨?_, c5⟩, ?_⟩
  · have w4 : Wrote b3 b4 [] tagT := ⟨by rw [k4.same.out]; simp, k4.same.ip, k4.same.ram, k4.same.rc, k4.same.kin,
      k4.same.kout, k4.same.kc, k4.fr.weaken hzT⟩
    have hw := (w03.trans w4).trans (w5.weaken hnT)
    have hint : NearCubicGates.Close.Interfaces.intWord (coefOf s) = natWord (if s then 0 else 1) ++ natWord 2 := by
      cases s <;> rfl
    rw [hint, marksD_append, marksD_append]
    simpa using hw
  · have k1 := hcost _ hv0
    have k2 := hcost 2 (by omega)
    have k3 := hcost _ hz
    omega

end NearQuarticWires.Reconstruct
