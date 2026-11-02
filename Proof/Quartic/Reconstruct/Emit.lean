import Proof.Gates.Cells.Kit

/-!
# Writing framed words in the cell language

The words between the stages of the reconstruction are framed (`RepairOrdinary.frame`), and the frames nest: a word
inside a frame inside the output frame is written with two levels of marks. In the base cell language
(`Gates/Cells/Lang`) one output operation writes one bit. This file writes a bit, a list of bits and a `natWord` at
any depth `d` of marks: each logical bit `b` becomes `2^d - 1` marks `true` followed by `b` (`bitD`, `marksD`), so
that `marksD d w` is `w` with `d` levels of marks (`marksD_succ`).

* `emitList_spec`: a fixed list of bits;
* `emitBD_spec`: the bit held in a variable, at depth `d`;
* `emitNatD_spec`: `natWord` of the variable `t3`, at depth `d` (the procedure of `Cells.emitNat` with every
  output operation replaced by its depth-`d` form).
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells
open NearCubicWires.RepairOrdinary.Streaming (marks)

variable {C : Ctx}

/-! ## Marks at depth `d` -/

/-- One logical bit at depth `d`: `2^d - 1` marks, then the bit. -/
def bitD (d : ℕ) (b : Bool) : List Bool := List.replicate (2 ^ d - 1) true ++ [b]

/-- A word at depth `d` of marks. -/
def marksD (d : ℕ) (w : List Bool) : List Bool := w.flatMap (bitD d)

theorem bitD_length (d : ℕ) (b : Bool) : (bitD d b).length = 2 ^ d := by
  have := Nat.one_le_two_pow (n := d)
  simp [bitD]
  omega

theorem marksD_append (d : ℕ) (u w : List Bool) : marksD d (u ++ w) = marksD d u ++ marksD d w := by
  simp [marksD]

theorem marksD_nil (d : ℕ) : marksD d [] = [] := rfl

theorem marksD_cons (d : ℕ) (b : Bool) (w : List Bool) : marksD d (b :: w) = bitD d b ++ marksD d w := by
  simp [marksD]

theorem marksD_length (d : ℕ) (w : List Bool) : (marksD d w).length = 2 ^ d * w.length := by
  induction w with
  | nil => simp [marksD]
  | cons b w ih => rw [marksD_cons, List.length_append, bitD_length, ih, List.length_cons]; ring

theorem marks_eq_flatMap (w : List Bool) : marks w = w.flatMap fun b => [true, b] := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    rw [List.flatMap_cons, ← ih]
    rfl

/-- `marksD 0 w = w`. -/
theorem marksD_zero (w : List Bool) : marksD 0 w = w := by
  induction w with
  | nil => rfl
  | cons b w ih => rw [marksD_cons, ih]; rfl

/-- **One more level of marks.** -/
theorem marksD_succ (d : ℕ) (w : List Bool) : marksD (d + 1) w = marks (marksD d w) := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    rw [marksD_cons, marksD_cons, ih, marks_eq_flatMap, marks_eq_flatMap, List.flatMap_append]
    congr 1
    unfold bitD
    rw [List.flatMap_append, List.flatMap_singleton]
    have h : 2 ^ (d + 1) - 1 = 2 * (2 ^ d - 1) + 1 := by
      have := Nat.one_le_two_pow (n := d)
      rw [pow_succ]
      omega
    rw [h, List.replicate_succ', List.append_assoc]
    congr 1
    · induction 2 ^ d - 1 with
      | zero => rfl
      | succ k ih' =>
        rw [List.replicate_succ, List.flatMap_cons, ← ih', show 2 * (k + 1) = 2 + 2 * k by ring,
          List.replicate_add]
        rfl

/-! ## Writing -/

/-- Only the output grows (by `w`), and only the variables in `T` change. -/
structure Wrote (a b : DS VV MM) (w : List Bool) (T : List (Fin VV)) : Prop where
  out : b.out = a.out ++ w
  ip : b.ip = a.ip
  ram : b.ram = a.ram
  rc : b.rc = a.rc
  kin : b.kin = a.kin
  kout : b.kout = a.kout
  kc : b.kc = a.kc
  fr : Fr a b T

theorem Wrote.refl (a : DS VV MM) (T : List (Fin VV)) : Wrote a a [] T :=
  ⟨by simp, rfl, rfl, rfl, rfl, rfl, rfl, Fr.refl a T⟩

theorem Wrote.trans {a b c : DS VV MM} {w w' : List Bool} {T : List (Fin VV)} (h1 : Wrote a b w T)
    (h2 : Wrote b c w' T) : Wrote a c (w ++ w') T :=
  ⟨by rw [h2.out, h1.out, List.append_assoc], h2.ip.trans h1.ip, h2.ram.trans h1.ram, h2.rc.trans h1.rc,
    h2.kin.trans h1.kin, h2.kout.trans h1.kout, h2.kc.trans h1.kc, Fr.trans h1.fr h2.fr⟩

theorem Wrote.set {a b : DS VV MM} {w : List Bool} {T : List (Fin VV)} (h : Wrote a b w T) {x : Fin VV}
    (v : ℕ) (hx : x ∈ T) : Wrote a (b.set x v) w T :=
  ⟨h.out, h.ip, h.ram, h.rc, h.kin, h.kout, h.kc, Fr.trans h.fr (Fr.set b v hx)⟩

theorem Wrote.weaken {a b : DS VV MM} {w : List Bool} {T T' : List (Fin VV)} (h : Wrote a b w T)
    (hT : ∀ y ∈ T, y ∈ T') : Wrote a b w T' :=
  ⟨h.out, h.ip, h.ram, h.rc, h.kin, h.kout, h.kc, h.fr.weaken hT⟩

theorem Wrote.cst {a b : DS VV MM} {w : List Bool} {T : List (Fin VV)} (h : Wrote a b w T) (hc : Cst a)
    (hT : vZ ∉ T ∧ v1 ∉ T ∧ v2 ∉ T) : Cst b := Cst.of_fr hc h.fr hT

/-- Write a fixed list of bits. -/
def emitList : List Bool → St VV MM
  | [] => skipS
  | b :: l => .seq (.op (.emit b)) (emitList l)

theorem emitList_spec (l : List Bool) (a : DS VV MM) :
    Hs C (emitList l) a (2 * l.length + 1) (fun b => Wrote a b l [vJ]) := by
  induction l generalizing a with
  | nil =>
    refine Hs.mono (skip_spec a) le_rfl ?_
    rintro b rfl
    exact (Wrote.refl a [vJ]).set 0 (by simp)
  | cons x l ih =>
    refine Hs.mono (Hs.seq (t2 := 2 * l.length + 1) (hs_emit C x a) (fun b hb => ?_)) (by simp; omega)
      (fun _ h => h)
    subst hb
    refine Hs.mono (ih _) le_rfl ?_
    intro c hc
    have h0 : Wrote a { a with out := a.out ++ [x] } [x] [vJ] :=
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, Fr.refl _ _⟩
    simpa using h0.trans hc

/-- One logical bit at depth `d`. -/
def putD (d : ℕ) (b : Bool) : St VV MM := emitList (bitD d b)

theorem putD_spec (d : ℕ) (b : Bool) (a : DS VV MM) :
    Hs C (putD d b) a (2 * 2 ^ d + 1) (fun c => Wrote a c (bitD d b) [vJ]) := by
  have h := emitList_spec (C := C) (bitD d b) a
  rwa [bitD_length] at h

/-- The bit held (as `0`/`1`) in `x`, at depth `d`. -/
def emitBD (d : ℕ) (x : Fin VV) : St VV MM := .ite (.eq x v1) (putD d true) (putD d false)

theorem emitBD_spec (d : ℕ) (x : Fin VV) (hx : x ≠ v1) (a : DS VV MM) (hc : Cst a) :
    Hs C (emitBD d x) a (2 * 2 ^ d + 2) (fun c => Wrote a c (bitD d (decide (a.env x = 1))) [vJ]) := by
  refine Hs.ite (c := .eq x v1) hx (fun he => ?_) (fun he => ?_)
  · have hx1 : a.env x = 1 := by simpa [Cnd.eval, hc.one] using he
    refine Hs.mono (putD_spec d true a) le_rfl ?_
    intro c hc'
    simpa [hx1] using hc'
  · have hx1 : a.env x ≠ 1 := by simpa [Cnd.eval, hc.one] using he
    refine Hs.mono (putD_spec d false a) le_rfl ?_
    intro c hc'
    simpa [hx1] using hc'

/-! ## `natWord` at depth `d` -/

/-- Write `natWord (t3)` at depth `d`. Scratch `t5 … t9` and `vJ`. -/
def emitNatD (d : ℕ) : St VV MM :=
  .seq (.op (.copy t5 t3)) (.seq (.op (.zero t6)) (.seq (.loop (.lt v1 t5) (.seq (.op (.half t5)) (.op (.inc t6))))
    (.seq (.op (.inc t6)) (.seq (.op (.zero t7)) (.seq (.loop (.lt t7 t6) (.seq (putD d true) (.op (.inc t7))))
      (.seq (putD d false) (.seq (.op (.copy t5 t3)) (.seq (.op (.zero t7))
        (.loop (.lt t7 t6) (.seq (.op (.dm t5 v2 t8 t9)) (.seq (emitBD d t9) (.seq (.op (.copy t5 t8))
          (.op (.inc t7))))))))))))))

/-- The scratch variables of `emitNatD`. -/
def emitNatDT : List (Fin VV) := [t5, t6, t7, t8, t9, vJ]

/-- The cost of `emitNatD d` on a value of bit length `ℓ`. -/
def emitNatDCost (d ℓ : ℕ) : ℕ := (4 * 2 ^ d + 20) * (ℓ + 3)

theorem emitNatD_spec (d : ℕ) (a : DS VV MM) (hc : Cst a) (hW : 2 ≤ C.Wd)
    (hv : natBitLength (a.env t3) + 2 < 2 ^ C.Wd) :
    Hs C (emitNatD d) a (emitNatDCost d (natBitLength (a.env t3)))
      (fun b => Wrote a b (marksD d (natWord (a.env t3))) emitNatDT ∧ Cst b) := by
  set v := a.env t3 with hvdef
  set ℓ := natBitLength v with hℓ
  have hℓl : ℓ = Nat.log 2 v + 1 := rfl
  have hv1 := hc.one
  have hv2 := hc.two
  have h4 : (4 : ℕ) ≤ 2 ^ C.Wd := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (by norm_num) hW
  have hTJ : vJ ∈ emitNatDT := by decide
  have hsub : ∀ y ∈ [vJ], y ∈ emitNatDT := by intro y hy; simp at hy; subst hy; decide
  have hcT : vZ ∉ emitNatDT ∧ v1 ∉ emitNatDT ∧ v2 ∉ emitNatDT := by decide
  -- loop 1: the logarithm
  let I1 : ℕ → DS VV MM → Prop := fun k b => b.env t5 = v / 2 ^ k ∧ b.env t6 = k ∧ Wrote a b [] emitNatDT
  have l1 : ∀ b, I1 0 b → Hs C (.loop (.lt v1 t5) (.seq (.op (.half t5)) (.op (.inc t6)))) b
      (Nat.log 2 v * (3 + 2) + 2) (I1 (Nat.log 2 v)) := by
    refine Hs.loopN (c := .lt v1 t5) (show v1 ≠ t5 by decide) I1 _ 3 ?_ ?_
    · intro k hk b ⟨h1, h2, h3⟩
      have bv1 : b.env v1 = 1 := by rw [h3.fr v1 (by decide)]; exact hv1
      refine ⟨by simp only [Cnd.eval, bv1, h1, decide_eq_true_eq]; exact (lt_div_iff_lt_log v k hk.le).2 hk, ?_⟩
      refine Hs.seq (t1 := 1) (t2 := 1) (hs_half C t5 b) (fun e he => ?_)
      subst he
      refine Hs.mono (hs_inc C t6 _ (by vsimp [h2]; omega)) le_rfl ?_
      rintro f rfl
      exact ⟨by vsimp [h1, Nat.div_div_eq_div_mul, pow_succ], by vsimp [h2],
        (h3.set _ (by decide)).set _ (by decide)⟩
    · intro b ⟨h1, _, h3⟩
      have bv1 : b.env v1 = 1 := by rw [h3.fr v1 (by decide)]; exact hv1
      simp only [Cnd.eval, bv1, h1, decide_eq_false_iff_not]
      exact fun h => absurd ((lt_div_iff_lt_log v _ le_rfl).1 h) (lt_irrefl _)
  -- loop 2: ℓ ones
  let I2 : ℕ → DS VV MM → Prop := fun k b => b.env t7 = k ∧ b.env t6 = ℓ ∧
    Wrote a b (marksD d (List.replicate k true)) emitNatDT
  have l2 : ∀ b, I2 0 b → Hs C (.loop (.lt t7 t6) (.seq (putD d true) (.op (.inc t7)))) b
      (ℓ * ((2 * 2 ^ d + 3) + 2) + 2) (I2 ℓ) := by
    refine Hs.loopN (c := .lt t7 t6) (show t7 ≠ t6 by decide) I2 _ (2 * 2 ^ d + 3) ?_ ?_
    · intro k hk b ⟨h1, h2, h3⟩
      refine ⟨by simp [Cnd.eval, h1, h2, hk], ?_⟩
      refine Hs.seq (t1 := 2 * 2 ^ d + 1) (t2 := 1) (putD_spec d true b) (fun e he => ?_)
      have e7 : e.env t7 = k := by rw [he.fr t7 (by decide), h1]
      have e6 : e.env t6 = ℓ := by rw [he.fr t6 (by decide), h2]
      refine Hs.mono (hs_inc C t7 e (by rw [e7]; omega)) le_rfl ?_
      rintro f rfl
      refine ⟨by vsimp [e7], by vsimp [e6], ?_⟩
      have hw := (h3.trans (he.weaken hsub)).set (x := t7) (e.env t7 + 1) (by decide)
      rw [List.replicate_succ', marksD_append]
      simpa [marksD] using hw
    · intro b ⟨h1, h2, _⟩
      simp [Cnd.eval, h1, h2]
  -- loop 3: the bits
  let I3 : ℕ → DS VV MM → Prop := fun k b => b.env t7 = k ∧ b.env t6 = ℓ ∧ b.env t5 = v / 2 ^ k ∧
    Wrote a b (marksD d (List.replicate ℓ true ++ [false] ++ (List.range k).map v.testBit)) emitNatDT
  have l3 : ∀ b, I3 0 b → Hs C (.loop (.lt t7 t6) (.seq (.op (.dm t5 v2 t8 t9)) (.seq (emitBD d t9)
      (.seq (.op (.copy t5 t8)) (.op (.inc t7)))))) b (ℓ * ((2 * 2 ^ d + 8) + 2) + 2) (I3 ℓ) := by
    refine Hs.loopN (c := .lt t7 t6) (show t7 ≠ t6 by decide) I3 _ (2 * 2 ^ d + 8) ?_ ?_
    · intro k hk b ⟨h1, h2, h3, h5⟩
      have bv1 : b.env v1 = 1 := by rw [h5.fr v1 (by decide)]; exact hv1
      have bv2 : b.env v2 = 2 := by rw [h5.fr v2 (by decide)]; exact hv2
      have bvZ : b.env vZ = 0 := by rw [h5.fr vZ (by decide)]; exact hc.z
      refine ⟨by simp [Cnd.eval, h1, h2, hk], ?_⟩
      refine Hs.mono (Hs.seq (t1 := 1) (t2 := 2 * 2 ^ d + 6) (hs_dm C t5 v2 t8 t9 b (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by rw [bv2]; norm_num) (by rw [bv2]; omega))
        (fun e he => ?_)) (by omega) (fun _ h => h)
      subst he
      set e := (b.set t8 (b.env t5 / b.env v2)).set t9 (b.env t5 % b.env v2) with hedef
      have ec : Cst e := ⟨by vsimp [hedef, bvZ], by vsimp [hedef, bv1], by vsimp [hedef, bv2]⟩
      have ew : Wrote a e (marksD d (List.replicate ℓ true ++ [false] ++ (List.range k).map v.testBit))
          emitNatDT := (h5.set _ (by decide)).set _ (by decide)
      have e9 : e.env t9 = v / 2 ^ k % 2 := by vsimp [hedef, h3, bv2]
      have e8 : e.env t8 = v / 2 ^ k / 2 := by vsimp [hedef, h3, bv2]
      refine Hs.seq (t1 := 2 * 2 ^ d + 2) (t2 := 3) (emitBD_spec d t9 (by decide) e ec) (fun f hf => ?_)
      have f8 : f.env t8 = v / 2 ^ k / 2 := by rw [hf.fr t8 (by decide), e8]
      have f7 : f.env t7 = k := by rw [hf.fr t7 (by decide)]; vsimp [hedef, h1]
      have f6 : f.env t6 = ℓ := by rw [hf.fr t6 (by decide)]; vsimp [hedef, h2]
      refine Hs.seq (t1 := 1) (t2 := 1) (hs_copy C t5 t8 f (by decide)) (fun g hg => ?_)
      subst hg
      refine Hs.mono (hs_inc C t7 _ (by vsimp [f7]; omega)) le_rfl ?_
      rintro g rfl
      refine ⟨by vsimp [f7], by vsimp [f6], by vsimp [f8, Nat.div_div_eq_div_mul, pow_succ], ?_⟩
      have hb : decide (e.env t9 = 1) = v.testBit k := by rw [e9, Nat.testBit_eq_decide_div_mod_eq]
      have hw := ((ew.trans (hf.weaken hsub)).set (x := t5) (f.env t8) (by decide)).set (x := t7)
        ((f.set t5 (f.env t8)).env t7 + 1) (by decide)
      rw [hb] at hw
      rw [List.range_succ, List.map_append, List.map_singleton, ← List.append_assoc, marksD_append
        (u := List.replicate ℓ true ++ [false] ++ (List.range k).map v.testBit)]
      simpa [marksD] using hw
    · intro b ⟨h1, h2, _⟩
      simp [Cnd.eval, h1, h2]
  -- the whole
  have hlogℓ : Nat.log 2 v < ℓ := by omega
  refine Hx.hs (Hs.then (hs_copy C t5 t3 a (by decide)) (fun b0 hb0 n0 hn0 => ?_))
  subst hb0
  refine Hs.then (hs_zero C t6 _) (fun b1 hb1 n1 hn1 => ?_)
  subst hb1
  refine Hs.then (l1 _ ⟨by vsimp [hvdef], by vsimp [], ((Wrote.refl a _).set _ (by decide)).set _ (by decide)⟩)
    (fun b2 hb2 n2 hn2 => ?_)
  obtain ⟨q1, q2, q3⟩ := hb2
  refine Hs.then (hs_inc C t6 b2 (by rw [q2]; omega)) (fun b3 hb3 n3 hn3 => ?_)
  subst hb3
  refine Hs.then (hs_zero C t7 _) (fun b4 hb4 n4 hn4 => ?_)
  subst hb4
  refine Hs.then (l2 _ ⟨by vsimp [], by vsimp [q2, hℓl], ?_⟩) (fun b5 hb5 n5 hn5 => ?_)
  · simpa [marksD] using (q3.set _ (by decide)).set _ (by decide)
  obtain ⟨r1, r2, r5⟩ := hb5
  refine Hs.then (putD_spec d false b5) (fun b6 hb6 n6 hn6 => ?_)
  have b6t3 : b6.env t3 = v := by rw [hb6.fr t3 (by decide), r5.fr t3 (by decide)]
  have b6t6 : b6.env t6 = ℓ := by rw [hb6.fr t6 (by decide), r2]
  refine Hs.then (hs_copy C t5 t3 _ (by decide)) (fun b7 hb7 n7 hn7 => ?_)
  subst hb7
  refine Hs.then (hs_zero C t7 _) (fun b8 hb8 n8 hn8 => ?_)
  subst hb8
  refine Hs.last (l3 _ ⟨by vsimp [], by vsimp [b6t6], by vsimp [b6t3], ?_⟩) ?_
  · have hw := (((r5.trans (hb6.weaken hsub)).set (x := t5) (b6.env t3) (by decide)).set (x := t7) 0
      (by decide))
    simpa [marksD_append, marksD] using hw
  · rintro g ⟨g1, g2, g3, g4⟩ n9 hn9
    refine ⟨⟨?_, g4.cst hc hcT⟩, ?_⟩
    · have hnat : natWord v = List.replicate ℓ true ++ [false] ++ (List.range ℓ).map v.testBit := by
        rw [natWord_eq, ofFn_testBit, ← hℓ]
        simp
      rw [hnat]
      exact g4
    · unfold emitNatDCost
      have hp : 1 ≤ 2 ^ d := Nat.one_le_two_pow
      nlinarith

end NearQuarticWires.Reconstruct
