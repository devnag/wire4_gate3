import Proof.Gates.Dispatch.Expr
import Mathlib.Data.Rat.Floor

/-!
# Exact outward rounding with binary natural arithmetic

Paper: `sec:algorithm`, paper/paper.tex. For a positive
denominator, ceiling is computed by adding the denominator minus one before
division. Signed differences are rounded by comparing their natural parts.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageOutput

open NearCubicGates.Close.Dispatch

def ceilQuot (n d : ℕ) : ℕ := (n + d - 1) / d

theorem ceilQuot_eq (n d : ℕ) (hd : 0 < d) :
    (ceilQuot n d : ℤ) = ⌈(n : ℚ) / d⌉ := by
  set q := ceilQuot n d
  have h₁ : q * d ≤ n + d - 1 := Nat.div_mul_le_self _ _
  have h₂ : n + d - 1 < d * (q + 1) := Nat.lt_mul_div_succ _ hd
  have he : n + d - 1 + 1 = n + d := by omega
  have hlow : q * d < n + d := by omega
  have hupp : n ≤ q * d := by nlinarith
  symm
  apply Int.ceil_eq_iff.mpr
  have hd' : (0 : ℚ) < d := by exact_mod_cast hd
  constructor
  · rw [lt_div_iff₀ hd']
    have h : (q : ℚ) * d < n + d := by exact_mod_cast hlow
    push_cast
    nlinarith
  · rw [div_le_iff₀ hd']
    exact_mod_cast hupp

/-- The magnitude of a nonnegative rounded quotient. -/
def quotientMagnitude (up : Bool) (n d : ℕ) : ℕ :=
  if up then ceilQuot n d else n / d

/-- Signed rounding of a difference of natural numbers. -/
def differenceRound (up : Bool) (x y d : ℕ) : ℤ :=
  if x < y then -(quotientMagnitude (!up) (y - x) d : ℤ)
  else (quotientMagnitude up (x - y) d : ℤ)

theorem differenceRound_floor (x y d : ℕ) (hd : 0 < d) :
    differenceRound false x y d = ⌊((x : ℚ) - y) / d⌋ := by
  unfold differenceRound
  split_ifs with h
  · have he : ((x : ℚ) - y) / d = -((y - x : ℕ) : ℚ) / d := by
      rw [Nat.cast_sub (by omega)]; ring
    rw [he, neg_div, Int.floor_neg]
    simp only [Bool.not_false, quotientMagnitude, ↓reduceIte]
    rw [ceilQuot_eq _ _ hd]
  · have he : ((x : ℚ) - y) / d = ((x - y : ℕ) : ℚ) / d := by
      rw [Nat.cast_sub (by omega)]
    rw [he, Rat.floor_natCast_div_natCast]
    rfl

theorem differenceRound_ceil (x y d : ℕ) (hd : 0 < d) :
    differenceRound true x y d = ⌈((x : ℚ) - y) / d⌉ := by
  unfold differenceRound
  split_ifs with h
  · have he : ((x : ℚ) - y) / d = -((y - x : ℕ) : ℚ) / d := by
      rw [Nat.cast_sub (by omega)]; ring
    rw [he, neg_div, Int.ceil_neg, Rat.floor_natCast_div_natCast]
    rfl
  · have he : ((x : ℚ) - y) / d = ((x - y : ℕ) : ℚ) / d := by
      rw [Nat.cast_sub (by omega)]
    rw [he]
    exact ceilQuot_eq _ _ hd

def roundX : Fin VV := ⟨40, by decide⟩
def roundY : Fin VV := ⟨41, by decide⟩
def roundD : Fin VV := ⟨42, by decide⟩
def roundQ : Fin VV := ⟨43, by decide⟩
def roundSign : Fin VV := ⟨44, by decide⟩

def quotientExpr (up : Bool) (x y : Fin VV) : AE :=
  let diff := AE.sub (.var x) (.var y)
  .div (if up then .sub (.add diff (.var roundD)) (.lit 1) else diff) (.var roundD)

def roundProgram (up : Bool) : St VV :=
  .ite (.lt roundX roundY)
    (.seq (assign roundSign (.lit 1)) (assign roundQ (quotientExpr (!up) roundY roundX)))
    (.seq (assign roundSign (.lit 0)) (assign roundQ (quotientExpr up roundX roundY)))

theorem quotientExpr_eval (up : Bool) (x y : Fin VV) (env : Fin VV → ℕ) :
    (quotientExpr up x y).eval env = quotientMagnitude up (env x - env y) (env roundD) := by
  cases up <;> rfl

theorem quotientAssign_spec {C : Ctx} (up : Bool) (x y : Fin VV)
    (hx : x.val < 200 ∧ x ≠ vJ) (hy : y.val < 200 ∧ y ≠ vJ)
    (a : DS VV) (hc : Cst a) (hd : 0 < a.env roundD)
    (hcap : a.env x + a.env y + a.env roundD + 2 < 2 ^ C.Wd)
    (hdiv : 2 * a.env roundD ≤ 2 ^ C.Wd) :
    Hs C (assign roundQ (quotientExpr up x y)) a 27 (fun b =>
      b.env roundQ = quotientMagnitude up (a.env x - a.env y) (a.env roundD) ∧
      AsgFr a b roundQ ∧ b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b) := by
  have hv : (quotientExpr up x y).vars_ok := by
    cases up <;> simp [quotientExpr, AE.vars_ok, hx, hy,
      show roundD.val < 200 from by decide, show roundD ≠ vJ from by decide]
  have hdep : (quotientExpr up x y).depth + 1 < 50 := by
    cases up <;> norm_num [quotientExpr, AE.depth, AE.cost]
  have hok : (quotientExpr up x y).ok C.Wd a.env := by
    cases up
    · exact ⟨⟨trivial, trivial⟩, trivial, hd, hdiv⟩
    · exact ⟨⟨⟨⟨trivial, trivial⟩, trivial, by change a.env x - a.env y + a.env roundD < _; omega⟩, by change 1 < _; omega⟩, trivial, hd, hdiv⟩
  have hcost : (quotientExpr up x y).cost + 2 ≤ 27 := by
    cases up <;> norm_num [quotientExpr, AE.depth, AE.cost]
  refine Hs.mono (assign_spec roundQ (by decide) (by decide) _ a hv hdep hc hok) hcost ?_
  rintro b ⟨hb, hfr, hcp, hwq, hout, hbc⟩
  exact ⟨by rw [hb, quotientExpr_eval], hfr, hcp, hwq, hout, hbc⟩

theorem roundBranch_spec {C : Ctx} (up : Bool) (x y : Fin VV)
    (hx : x.val < 200 ∧ x ≠ vJ ∧ x ≠ roundSign)
    (hy : y.val < 200 ∧ y ≠ vJ ∧ y ≠ roundSign)
    (sg : ℕ) (hsg : sg ≤ 1) (a : DS VV) (hc : Cst a)
    (hd : 0 < a.env roundD)
    (hcap : a.env x + a.env y + a.env roundD + 2 < 2 ^ C.Wd)
    (hdiv : 2 * a.env roundD ≤ 2 ^ C.Wd) :
    Hs C (.seq (assign roundSign (.lit sg)) (assign roundQ (quotientExpr up x y))) a 35
      (fun b => b.env roundSign = sg ∧
        b.env roundQ = quotientMagnitude up (a.env x - a.env y) (a.env roundD) ∧
        b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
        ∀ z : Fin VV, z.val < 200 → z ≠ vJ → z ≠ roundSign → z ≠ roundQ → b.env z = a.env z) := by
  refine Hs.mono (Hs.seq (t1 := 7) (t2 := 27)
    (Hs.mono (assign_spec roundSign (by decide) (by decide) (.lit sg) a trivial
      (by norm_num [AE.depth]) hc (by change sg < _; omega)) (by change 2 * sg + 3 + 2 ≤ 7; omega)
      (fun b h => h)) (fun b hb => ?_)) le_rfl (fun _ h => h)
  obtain ⟨hbsg, hbfr, hbcp, hbwq, hbout, hbc⟩ := hb
  have hbx : b.env x = a.env x := hbfr x hx.1 hx.2.1 hx.2.2
  have hby : b.env y = a.env y := hbfr y hy.1 hy.2.1 hy.2.2
  have hbd : b.env roundD = a.env roundD := hbfr roundD (by decide) (by decide) (by decide)
  refine Hs.mono (quotientAssign_spec up x y ⟨hx.1, hx.2.1⟩ ⟨hy.1, hy.2.1⟩ b hbc
    (by rw [hbd]; exact hd) (by rw [hbx, hby, hbd]; exact hcap)
    (by rw [hbd]; exact hdiv)) le_rfl ?_
  rintro d ⟨hdq, hdfr, hdcp, hdwq, hdout, hdc⟩
  refine ⟨?_, by rw [hdq, hbx, hby, hbd], by rw [hdcp, hbcp], by rw [hdwq, hbwq],
    by rw [hdout, hbout], hdc, ?_⟩
  · rw [hdfr roundSign (by decide) (by decide) (by decide)]
    exact hbsg
  · intro z hz hzj hzs hzq
    rw [hdfr z hz hzj hzq, hbfr z hz hzj hzs]

theorem roundProgram_spec {C : Ctx} (up : Bool) (a : DS VV) (hc : Cst a)
    (hd : 0 < a.env roundD)
    (hcap : a.env roundX + a.env roundY + a.env roundD + 2 < 2 ^ C.Wd)
    (hdiv : 2 * a.env roundD ≤ 2 ^ C.Wd) :
    Hs C (roundProgram up) a 36 (fun b =>
      (if b.env roundSign = 0 then (b.env roundQ : ℤ) else -(b.env roundQ : ℤ)) =
        differenceRound up (a.env roundX) (a.env roundY) (a.env roundD) ∧
      b.env roundSign ≤ 1 ∧ b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      ∀ z : Fin VV, z.val < 200 → z ≠ vJ → z ≠ roundSign → z ≠ roundQ → b.env z = a.env z) := by
  refine Hs.ite (c := .lt roundX roundY) (show roundX ≠ roundY by decide) (fun h => ?_) (fun h => ?_)
  · have hxy : a.env roundX < a.env roundY := by simpa [Cnd.eval] using h
    refine Hs.mono (roundBranch_spec (!up) roundY roundX (by decide) (by decide) 1 (by omega)
      a hc hd (by omega) hdiv) le_rfl ?_
    rintro b ⟨hs, hq, hcp, hwq, hout, hbc, hfr⟩
    exact ⟨by simp [hs, hq, differenceRound, hxy], by omega, hcp, hwq, hout, hbc, hfr⟩
  · have hxy : ¬ a.env roundX < a.env roundY := by simpa [Cnd.eval] using h
    refine Hs.mono (roundBranch_spec up roundX roundY (by decide) (by decide) 0 (by omega)
      a hc hd hcap hdiv) le_rfl ?_
    rintro b ⟨hs, hq, hcp, hwq, hout, hbc, hfr⟩
    exact ⟨by simp [hs, hq, differenceRound, hxy], by omega, hcp, hwq, hout, hbc, hfr⟩

end NearQuarticWires.StageOutput
