import Proof.Quartic.Control.Call
import Proof.Wire_3_5.PrimAsmParseNat

/-!
# Comparing two integers written by a subroutine

Paper: Step 3 of `sec:algorithm`, paper/paper.tex: in each round the two children `π0`, `π1` of the
current prefix are evaluated and the bit of the child with the smaller value `Ψ̃` is appended (ties to `0`); this
is the greedy step `greedyStep R π = π ++ [decide (R (π1) < R (π0))]` (imported from `Proof.Wire_3_5.SeedFixGreedy`).

The two values are integers `intWord z = natWord s ++ natWord |z|`, written by a word function on an output tape.
`natWord x` is the unary length `1^L 0` followed by the `L` bits of `x`, lowest first, `L = natBitLength x`.

* `ltNat` decides `x < y` for two numbers `natWord x`, `natWord y` read on two streams in one pass: first the unary
  lengths (a shorter length is a smaller number), then, on equal lengths, the bits from the lowest to the highest,
  the last difference deciding (`ltNat_exec`).
* `ltInt` decides `b < a` for `intWord a` and `intWord b`, from the signs and `ltNat` on the magnitudes
  (`ltInt_exec`).

Both leave the streams and their heads as they found them and cost a constant times the length of the two words.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.Control

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (read_pre natWord_getD_one natWord_getD_zero
  natWord_getD_payload natWord_length)

variable {ns nr : ℕ}

/-! ## Arithmetic -/

/-- A shorter `natWord` is a smaller number. -/
theorem lt_of_natBitLength_lt {x y : ℕ} (h : natBitLength x < natBitLength y) : x < y := by
  unfold natBitLength at h
  by_contra hxy
  have := Nat.log_mono_right (b := 2) (not_lt.mp hxy)
  omega

theorem lt_two_pow_natBitLength (x : ℕ) : x < 2 ^ natBitLength x := by
  unfold natBitLength
  exact Nat.lt_pow_succ_log_self (by norm_num) x

theorem mod_two_pow_succ (x i : ℕ) : x % 2 ^ (i + 1) = x % 2 ^ i + 2 ^ i * (x.testBit i).toNat := by
  rw [Nat.mod_pow_succ]
  congr 2
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have := Nat.mod_two_eq_zero_or_one (x / 2 ^ i)
  rcases this with h | h <;> simp [h]

/-- The comparison of the low `i + 1` bits: the bit `i` decides when it differs. -/
theorem lt_mod_succ (x y i : ℕ) :
    decide (x % 2 ^ (i + 1) < y % 2 ^ (i + 1)) =
      if x.testBit i = y.testBit i then decide (x % 2 ^ i < y % 2 ^ i) else y.testBit i := by
  rw [mod_two_pow_succ x i, mod_two_pow_succ y i]
  have hx : x % 2 ^ i < 2 ^ i := Nat.mod_lt _ (by positivity)
  have hy : y % 2 ^ i < 2 ^ i := Nat.mod_lt _ (by positivity)
  generalize x % 2 ^ i = a at *
  generalize y % 2 ^ i = b at *
  generalize 2 ^ i = P at *
  cases x.testBit i <;> cases y.testBit i <;> simp <;> omega

/-! ## The state of a comparison -/

/-- The registers of a comparison: `F` (continue), `D` (decided), `K` (common length, then bits left), `M` (moves
of the two heads), `R` (the result). -/
structure CmpRegs (nr : ℕ) where
  /-- The five registers. -/
  r : Fin 5 ↪ Fin nr

/-- The state during a comparison of the streams `X`, `Y`: both heads moved by `j`, the five registers. -/
def cmpState (σ : WState ns nr) (X Y : Fin (ns + 1)) (G : Fin 5 ↪ Fin nr) (j f d k m r : ℕ) : WState ns nr :=
  ⟨Function.update (Function.update σ.sh X (σ.sh X + j)) Y (σ.sh Y + j), σ.st,
    fun q => if q = G 0 then f else if q = G 1 then d else if q = G 2 then k else if q = G 3 then m
      else if q = G 4 then r else σ.val q, σ.cell⟩

section State

variable (σ : WState ns nr) (X Y : Fin (ns + 1)) (G : Fin 5 ↪ Fin nr) (j f d k m r : ℕ)

theorem G_ne {a b : Fin 5} (h : a ≠ b) : G a ≠ G b := G.injective.ne h

@[simp] theorem cmpState_F : (cmpState σ X Y G j f d k m r).val (G 0) = f := by simp [cmpState]
@[simp] theorem cmpState_D : (cmpState σ X Y G j f d k m r).val (G 1) = d := by
  simp [cmpState, G_ne G (show (1 : Fin 5) ≠ 0 by decide)]
@[simp] theorem cmpState_K : (cmpState σ X Y G j f d k m r).val (G 2) = k := by
  simp [cmpState, G_ne G (show (2 : Fin 5) ≠ 0 by decide), G_ne G (show (2 : Fin 5) ≠ 1 by decide)]
@[simp] theorem cmpState_M : (cmpState σ X Y G j f d k m r).val (G 3) = m := by
  simp [cmpState, G_ne G (show (3 : Fin 5) ≠ 0 by decide), G_ne G (show (3 : Fin 5) ≠ 1 by decide),
    G_ne G (show (3 : Fin 5) ≠ 2 by decide)]
@[simp] theorem cmpState_R : (cmpState σ X Y G j f d k m r).val (G 4) = r := by
  simp [cmpState, G_ne G (show (4 : Fin 5) ≠ 0 by decide), G_ne G (show (4 : Fin 5) ≠ 1 by decide),
    G_ne G (show (4 : Fin 5) ≠ 2 by decide), G_ne G (show (4 : Fin 5) ≠ 3 by decide)]

theorem cmpState_wbitX (hXY : X ≠ Y) :
    wbit (cmpState σ X Y G j f d k m r) X = readTapeBit (σ.st X) (σ.sh X + j) := by
  simp [wbit, cmpState, Function.update_of_ne hXY]

theorem cmpState_wbitY : wbit (cmpState σ X Y G j f d k m r) Y = readTapeBit (σ.st Y) (σ.sh Y + j) := by
  simp [wbit, cmpState]

theorem cmpState_setF (v : ℕ) : (cmpState σ X Y G j f d k m r).setv (G 0) v = cmpState σ X Y G j v d k m r := by
  refine WState.eq rfl rfl ?_ rfl
  funext q; simp only [cmpState, WState.setv_val, Function.update_apply]
  split_ifs <;> simp_all

theorem cmpState_setD (v : ℕ) : (cmpState σ X Y G j f d k m r).setv (G 1) v = cmpState σ X Y G j f v k m r := by
  refine WState.eq rfl rfl ?_ rfl
  funext q; simp only [cmpState, WState.setv_val, Function.update_apply]
  split_ifs <;> simp_all [G_ne G (show (1 : Fin 5) ≠ 0 by decide)]

theorem cmpState_setK (v : ℕ) : (cmpState σ X Y G j f d k m r).setv (G 2) v = cmpState σ X Y G j f d v m r := by
  refine WState.eq rfl rfl ?_ rfl
  funext q; simp only [cmpState, WState.setv_val, Function.update_apply]
  split_ifs <;> simp_all [G_ne G (show (2 : Fin 5) ≠ 0 by decide), G_ne G (show (2 : Fin 5) ≠ 1 by decide)]

theorem cmpState_setM (v : ℕ) : (cmpState σ X Y G j f d k m r).setv (G 3) v = cmpState σ X Y G j f d k v r := by
  refine WState.eq rfl rfl ?_ rfl
  funext q; simp only [cmpState, WState.setv_val, Function.update_apply]
  split_ifs <;> simp_all [G_ne G (show (3 : Fin 5) ≠ 0 by decide), G_ne G (show (3 : Fin 5) ≠ 1 by decide),
    G_ne G (show (3 : Fin 5) ≠ 2 by decide)]

theorem cmpState_setR (v : ℕ) : (cmpState σ X Y G j f d k m r).setv (G 4) v = cmpState σ X Y G j f d k m v := by
  refine WState.eq rfl rfl ?_ rfl
  funext q; simp only [cmpState, WState.setv_val, Function.update_apply]
  split_ifs <;> simp_all [G_ne G (show (4 : Fin 5) ≠ 0 by decide), G_ne G (show (4 : Fin 5) ≠ 1 by decide),
    G_ne G (show (4 : Fin 5) ≠ 2 by decide), G_ne G (show (4 : Fin 5) ≠ 3 by decide)]

/-- The comparison state with nothing moved and the registers of `σ` at zero is `σ` with the result set. -/
theorem cmpState_zero (hz : ∀ i : Fin 5, σ.val (G i) = 0) (v : ℕ) :
    cmpState σ X Y G 0 0 0 0 0 v = σ.setv (G 4) v := by
  refine WState.eq ?_ rfl ?_ rfl
  · funext q; simp only [cmpState, WState.setv_sh, Nat.add_zero, Function.update_eq_self]
  · funext q; simp only [cmpState, WState.setv_val, Function.update_apply]
    split_ifs <;> simp_all

end State

/-! ## Moving the two heads together -/

/-- Both heads one cell right, `M := M + 1`. -/
def bothFwd (X Y : Fin (ns + 1)) (M : Fin nr) : WMX ns nr := .seq (WMX.fwd X) (.seq (WMX.fwd Y) (WMX.inc M))

/-- Both heads one cell left, `M := M − 1`. -/
def bothBwd (X Y : Fin (ns + 1)) (M : Fin nr) : WMX ns nr := .seq (WMX.dec M) (.seq (WMX.bwd X) (WMX.bwd Y))

theorem bothFwd_exec (cap : ℕ) (σ : WState ns nr) (X Y : Fin (ns + 1)) (G : Fin 5 ↪ Fin nr) (hXY : X ≠ Y)
    (j f d k m r : ℕ) (hc : m < cap) :
    WXExec cap (bothFwd X Y (G 3)) (cmpState σ X Y G j f d k m r) (cmpState σ X Y G (j + 1) f d k (m + 1) r) 7 := by
  have e1 := WXExec.fwd cap X (cmpState σ X Y G j f d k m r)
  set s1 := (cmpState σ X Y G j f d k m r).seth X ((cmpState σ X Y G j f d k m r).sh X + 1) with hs1
  have e2 := WXExec.fwd cap Y s1
  set s2 := s1.seth Y (s1.sh Y + 1) with hs2
  have e3 := WXExec.inc cap (G 3) s2 (by simp [hs2, hs1, hc])
  refine WXExec.cast cap (WXExec.seq e1 (WXExec.seq e2 e3)) ?_ le_rfl
  have hv : s2.val = (cmpState σ X Y G j f d k m r).val := rfl
  rw [hv, cmpState_M, ← cmpState_setM σ X Y G (j + 1) f d k m r (m + 1)]
  refine WState.eq ?_ rfl rfl rfl
  funext q
  by_cases hqY : q = Y
  · subst hqY; simp [hs2, hs1, cmpState, Function.update_of_ne hXY.symm]; omega
  · by_cases hqX : q = X
    · subst hqX; simp [hs2, hs1, cmpState, Function.update_of_ne hqY, hXY]; omega
    · simp [hs2, hs1, cmpState, Function.update_of_ne hqY, Function.update_of_ne hqX]

theorem bothBwd_exec (cap : ℕ) (σ : WState ns nr) (X Y : Fin (ns + 1)) (G : Fin 5 ↪ Fin nr) (hXY : X ≠ Y)
    (j f d k m r : ℕ) (hc : m + 1 ≤ cap) :
    WXExec cap (bothBwd X Y (G 3)) (cmpState σ X Y G (j + 1) f d k (m + 1) r) (cmpState σ X Y G j f d k m r) 5 := by
  have e1 := WXExec.dec cap (G 3) (cmpState σ X Y G (j + 1) f d k (m + 1) r) (by simp [hc])
  rw [cmpState_M, cmpState_setM, Nat.add_sub_cancel] at e1
  have e2 := WXExec.bwd cap X (cmpState σ X Y G (j + 1) f d k m r)
  set s1 := (cmpState σ X Y G (j + 1) f d k m r).seth X ((cmpState σ X Y G (j + 1) f d k m r).sh X - 1) with hs1
  have e3 := WXExec.bwd cap Y s1
  refine WXExec.cast cap (WXExec.seq e1 (WXExec.seq e2 e3)) ?_ (by omega)
  refine WState.eq ?_ rfl rfl rfl
  funext q
  by_cases hqY : q = Y
  · subst hqY; simp [hs1, cmpState, Function.update_of_ne hXY.symm]
  · by_cases hqX : q = X
    · subst hqX; simp [hs1, cmpState, Function.update_of_ne hqY, hXY]
    · simp [hs1, cmpState, Function.update_of_ne hqY, Function.update_of_ne hqX]


/-! ## `natWord` comparison -/

/-- `R := 0` for a register holding `0` or `1`. -/
def clrR (R : Fin nr) : WMX ns nr := .ifr R (WMX.dec R) WMX.skip

/-- `R := 1` for a register holding `0` or `1`. -/
def setR (R : Fin nr) : WMX ns nr := .ifr R WMX.skip (WMX.inc R)

/-- One step of the unary lengths: on `1, 1` both heads move on; otherwise the loop stops (`F := 0`), with
`D := 1` and the result `R` when the lengths differ. -/
def prefixBody (X Y : Fin (ns + 1)) (G : Fin 5 ↪ Fin nr) : WMX ns nr :=
  .ifs X
    (.ifs Y (.seq (bothFwd X Y (G 3)) (WMX.inc (G 2))) (.seq (WMX.dec (G 0)) (WMX.inc (G 1))))
    (.ifs Y (.seq (WMX.dec (G 0)) (.seq (WMX.inc (G 1)) (WMX.inc (G 4)))) (WMX.dec (G 0)))

/-- One bit of equal-length numbers: a difference sets `R` to the bit of `Y`; both heads move on. -/
def bitBody (X Y : Fin (ns + 1)) (G : Fin 5 ↪ Fin nr) : WMX ns nr :=
  .seq (.ifs X (.ifs Y WMX.skip (clrR (G 4))) (.ifs Y (setR (G 4)) WMX.skip)) (bothFwd X Y (G 3))

/-- **The comparison** `R := [x < y]` of `natWord x` on `X` and `natWord y` on `Y`. -/
def ltNat (X Y : Fin (ns + 1)) (G : Fin 5 ↪ Fin nr) : WMX ns nr :=
  .seq (WMX.inc (G 0))
  (.seq (.whr (G 0) (prefixBody X Y G))
  (.seq (.ifr (G 1) (.seq (WMX.dec (G 1)) (.whr (G 2) (WMX.dec (G 2))))
      (.seq (bothFwd X Y (G 3)) (.whr (G 2) (.seq (WMX.dec (G 2)) (bitBody X Y G)))))
  (.whr (G 3) (bothBwd X Y (G 3)))))

section LtNat

variable (cap : ℕ) (σ : WState ns nr) (X Y : Fin (ns + 1)) (G : Fin 5 ↪ Fin nr)

theorem prefixBody_exec (hXY : X ≠ Y) (j : ℕ) (hc : j + 1 < cap) :
    WXExec cap (prefixBody X Y G) (cmpState σ X Y G j 1 0 j j 0)
      (match readTapeBit (σ.st X) (σ.sh X + j), readTapeBit (σ.st Y) (σ.sh Y + j) with
        | true, true => cmpState σ X Y G (j + 1) 1 0 (j + 1) (j + 1) 0
        | true, false => cmpState σ X Y G j 0 1 j j 0
        | false, true => cmpState σ X Y G j 0 1 j j 1
        | false, false => cmpState σ X Y G j 0 0 j j 0) 13 := by
  have hbX := cmpState_wbitX σ X Y G j 1 0 j j 0 hXY
  have hbY := cmpState_wbitY σ X Y G j 1 0 j j 0
  have decF : ∀ d r : ℕ, WXExec cap (WMX.dec (G 0)) (cmpState σ X Y G j 1 d j j r) (cmpState σ X Y G j 0 d j j r)
      1 := by
    intro d r
    have := WXExec.dec cap (G 0) (cmpState σ X Y G j 1 d j j r) (by simp; omega)
    simpa [cmpState_setF] using this
  cases hx : readTapeBit (σ.st X) (σ.sh X + j) <;> cases hy : readTapeBit (σ.st Y) (σ.sh Y + j)
  · -- `0, 0`
    exact WXExec.mono (WXExec.ifsF (by rw [hbX, hx]) (WXExec.ifsF (by rw [hbY, hy]) (decF 0 0))) (by omega)
  · -- `0, 1`
    have e2 := WXExec.inc cap (G 1) (cmpState σ X Y G j 0 0 j j 0) (by simp; omega)
    rw [cmpState_D, cmpState_setD] at e2
    have e3 := WXExec.inc cap (G 4) (cmpState σ X Y G j 0 1 j j 0) (by simp; omega)
    rw [cmpState_R, cmpState_setR] at e3
    exact WXExec.mono (WXExec.ifsF (by rw [hbX, hx]) (WXExec.ifsT (by rw [hbY, hy])
      (WXExec.seq (decF 0 0) (WXExec.seq e2 e3)))) (by omega)
  · -- `1, 0`
    have e2 := WXExec.inc cap (G 1) (cmpState σ X Y G j 0 0 j j 0) (by simp; omega)
    rw [cmpState_D, cmpState_setD] at e2
    exact WXExec.mono (WXExec.ifsT (by rw [hbX, hx]) (WXExec.ifsF (by rw [hbY, hy])
      (WXExec.seq (decF 0 0) e2))) (by omega)
  · -- `1, 1`
    have e1 := bothFwd_exec cap σ X Y G hXY j 1 0 j j 0 (by omega)
    have e2 := WXExec.inc cap (G 2) (cmpState σ X Y G (j + 1) 1 0 j (j + 1) 0) (by simp; omega)
    rw [cmpState_K, cmpState_setK] at e2
    exact WXExec.mono (WXExec.ifsT (by rw [hbX, hx]) (WXExec.ifsT (by rw [hbY, hy]) (WXExec.seq e1 e2)))
      (by omega)

theorem bitBody_exec (hXY : X ≠ Y) (j k m : ℕ) (r : Bool) (hc : m + 1 < cap) :
    WXExec cap (bitBody X Y G) (cmpState σ X Y G j 0 0 k m r.toNat)
      (cmpState σ X Y G (j + 1) 0 0 k (m + 1)
        (if readTapeBit (σ.st X) (σ.sh X + j) = readTapeBit (σ.st Y) (σ.sh Y + j) then r
          else readTapeBit (σ.st Y) (σ.sh Y + j)).toNat) 15 := by
  have hbX := cmpState_wbitX σ X Y G j 0 0 k m r.toNat hXY
  have hbY := cmpState_wbitY σ X Y G j 0 0 k m r.toNat
  have clr : WXExec cap (clrR (G 4)) (cmpState σ X Y G j 0 0 k m r.toNat) (cmpState σ X Y G j 0 0 k m 0) 2 := by
    cases r
    · exact WXExec.mono (WXExec.ifrF (by simp) (WXExec.skip cap _)) (by omega)
    · have := WXExec.dec cap (G 4) (cmpState σ X Y G j 0 0 k m (true : Bool).toNat) (by simp; omega)
      rw [cmpState_R, cmpState_setR] at this
      exact WXExec.mono (WXExec.ifrT (by simp) this) (by omega)
  have set1 : WXExec cap (setR (G 4)) (cmpState σ X Y G j 0 0 k m r.toNat) (cmpState σ X Y G j 0 0 k m 1) 4 := by
    cases r
    · have := WXExec.inc cap (G 4) (cmpState σ X Y G j 0 0 k m (false : Bool).toNat) (by simp; omega)
      rw [cmpState_R, cmpState_setR] at this
      exact WXExec.mono (WXExec.ifrF (by simp) this) (by omega)
    · exact WXExec.mono (WXExec.ifrT (by simp) (WXExec.skip cap _)) (by omega)
  have fw := fun v => bothFwd_exec cap σ X Y G hXY j 0 0 k m v (by omega)
  cases hx : readTapeBit (σ.st X) (σ.sh X + j) <;> cases hy : readTapeBit (σ.st Y) (σ.sh Y + j)
  · exact WXExec.mono (WXExec.seq (WXExec.ifsF (by rw [hbX, hx]) (WXExec.ifsF (by rw [hbY, hy])
      (WXExec.skip cap _))) (fw _)) (by omega)
  · exact WXExec.mono (WXExec.seq (WXExec.ifsF (by rw [hbX, hx]) (WXExec.ifsT (by rw [hbY, hy]) set1)) (fw _))
      (by omega)
  · exact WXExec.mono (WXExec.seq (WXExec.ifsT (by rw [hbX, hx]) (WXExec.ifsF (by rw [hbY, hy]) clr)) (fw _))
      (by omega)
  · exact WXExec.mono (WXExec.seq (WXExec.ifsT (by rw [hbX, hx]) (WXExec.ifsT (by rw [hbY, hy])
      (WXExec.skip cap _))) (fw _)) (by omega)

/-- Reading inside a number written on a stream. -/
theorem read_natWord {pre rest : List Bool} {x : ℕ} (hst : σ.st X = pre ++ RepairRepresentation.natWord x ++ rest)
    (hsh : σ.sh X = pre.length) (j : ℕ) (hj : j < (RepairRepresentation.natWord x).length) :
    readTapeBit (σ.st X) (σ.sh X + j) = (RepairRepresentation.natWord x).getD j false := by
  rw [hst, hsh, List.append_assoc, read_pre]
  unfold readTapeBit
  rw [List.getD_append _ _ _ _ hj]

end LtNat


/-- The cost bound of `ltNat` on two numbers of bit lengths `Lx`, `Ly`. -/
def ltNatCost (Lx Ly : ℕ) : ℕ := 60 * (Lx + Ly + 2)

section LtNatExec

variable (cap : ℕ) (σ : WState ns nr) (X Y : Fin (ns + 1)) (G : Fin 5 ↪ Fin nr)

/-- The rewind of both heads by the move counter. -/
theorem rewind_exec (hXY : X ≠ Y) (J r : ℕ) (hc : J ≤ cap) :
    WXExec cap (.whr (G 3) (bothBwd X Y (G 3))) (cmpState σ X Y G J 0 0 0 J r) (cmpState σ X Y G 0 0 0 0 0 r)
      (J * 7 + 1) := by
  have h := Runs.whr (cap := cap) (r := G 3) (P := bothBwd X Y (G 3))
    (fun k τ => k ≤ J ∧ τ = cmpState σ X Y G k 0 0 0 k r) 5 (fun τ => τ = cmpState σ X Y G 0 0 0 0 0 r)
    (by rintro τ ⟨-, rfl⟩; exact ⟨by simp, rfl⟩)
    (by
      rintro k τ ⟨hk, rfl⟩
      exact ⟨by simp, Runs.of (bothBwd_exec cap σ X Y G hXY k 0 0 0 k r (by omega)) ⟨by omega, rfl⟩⟩)
    J _ ⟨le_rfl, rfl⟩
  obtain ⟨τ, e, rfl⟩ := h
  exact e

/-- Clearing a counter. -/
theorem clearK_exec (j k m r : ℕ) (hc : k ≤ cap) :
    WXExec cap (.whr (G 2) (WMX.dec (G 2))) (cmpState σ X Y G j 0 0 k m r) (cmpState σ X Y G j 0 0 0 m r)
      (k * 3 + 1) := by
  have h := Runs.whr (cap := cap) (r := G 2) (P := WMX.dec (G 2))
    (fun i τ => i ≤ k ∧ τ = cmpState σ X Y G j 0 0 i m r) 1 (fun τ => τ = cmpState σ X Y G j 0 0 0 m r)
    (by rintro τ ⟨-, rfl⟩; exact ⟨by simp, rfl⟩)
    (by
      rintro i τ ⟨hi, rfl⟩
      have e := WXExec.dec cap (G 2) (cmpState σ X Y G j 0 0 (i + 1) m r) (by simp; omega)
      rw [cmpState_K, cmpState_setK, Nat.add_sub_cancel] at e
      exact ⟨by simp, Runs.of e ⟨by omega, rfl⟩⟩)
    k _ ⟨le_rfl, rfl⟩
  obtain ⟨τ, e, rfl⟩ := h
  exact e

/-- **`ltNat` decides `x < y`.** From the heads at the starts of `natWord x` on `X` and `natWord y` on `Y` and the
five registers at zero, `ltNat` sets `R` to `[x < y]` and leaves everything else as it was. -/
theorem ltNat_exec (hXY : X ≠ Y) {pX rX pY rY : List Bool} (x y : ℕ)
    (hX : σ.st X = pX ++ RepairRepresentation.natWord x ++ rX) (hXh : σ.sh X = pX.length)
    (hY : σ.st Y = pY ++ RepairRepresentation.natWord y ++ rY) (hYh : σ.sh Y = pY.length)
    (hz : ∀ i, σ.val (G i) = 0) (hc : 2 * natBitLength x + 2 * natBitLength y + 4 ≤ cap) :
    WXExec cap (ltNat X Y G) σ (σ.setv (G 4) (decide (x < y)).toNat)
      (ltNatCost (natBitLength x) (natBitLength y)) := by
  set Lx := natBitLength x with hLx
  set Ly := natBitLength y with hLy
  have lenX := natWord_length x
  have lenY := natWord_length y
  have readX : ∀ j, j ≤ Lx → readTapeBit (σ.st X) (σ.sh X + j) = decide (j < Lx) := by
    intro j hj
    rw [read_natWord σ X hX hXh j (by omega)]
    rcases Nat.lt_or_ge j Lx with h | h
    · rw [natWord_getD_one x j h]; simp [h]
    · have : j = Lx := by omega
      subst this; rw [natWord_getD_zero]; simp
  have readY : ∀ j, j ≤ Ly → readTapeBit (σ.st Y) (σ.sh Y + j) = decide (j < Ly) := by
    intro j hj
    rw [read_natWord σ Y hY hYh j (by omega)]
    rcases Nat.lt_or_ge j Ly with h | h
    · rw [natWord_getD_one y j h]; simp [h]
    · have : j = Ly := by omega
      subst this; rw [natWord_getD_zero]; simp
  have hσ0 : cmpState σ X Y G 0 0 0 0 0 0 = σ := by
    rw [cmpState_zero σ X Y G hz 0]; exact BinW.setv_same (hz 4)
  -- start: `F := 1`
  have e0 := WXExec.inc cap (G 0) (cmpState σ X Y G 0 0 0 0 0 0) (by simp; omega)
  rw [cmpState_F, cmpState_setF, Nat.zero_add] at e0
  -- phase 1: the unary lengths
  set m := min Lx Ly with hm
  set fin1 := if Lx = Ly then cmpState σ X Y G m 0 0 m m 0 else if Ly < Lx then cmpState σ X Y G m 0 1 m m 0
    else cmpState σ X Y G m 0 1 m m 1 with hfin1
  have p1 := Runs.whr (cap := cap) (r := G 0) (P := prefixBody X Y G)
    (fun k τ => (k = 0 ∧ τ = fin1) ∨ (1 ≤ k ∧ k ≤ m + 1 ∧ τ = cmpState σ X Y G (m + 1 - k) 1 0 (m + 1 - k)
      (m + 1 - k) 0)) 13 (fun τ => τ = fin1)
    (by
      rintro τ (⟨-, rfl⟩ | ⟨h, -⟩)
      · refine ⟨?_, rfl⟩
        rw [hfin1]; split_ifs <;> simp
      · omega)
    (by
      rintro k τ (⟨h, -⟩ | ⟨-, hk, rfl⟩)
      · omega
      refine ⟨by simp, ?_⟩
      have e := prefixBody_exec cap σ X Y G hXY (m + 1 - (k + 1)) (by omega)
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst hk0
        have hj : m + 1 - (0 + 1) = m := by omega
        rw [hj] at e ⊢
        rw [readX m (by omega), readY m (by omega)] at e
        refine Runs.of e (Or.inl ⟨rfl, ?_⟩)
        rw [hfin1]
        rcases Nat.lt_trichotomy Lx Ly with h | h | h
        · have h1 : m = Lx := by omega
          rw [if_neg (by omega), if_neg (by omega)]
          simp [h1, h]
        · have h1 : m = Lx := by omega
          rw [if_pos h]
          simp [h1, h]
        · have h1 : m = Ly := by omega
          rw [if_neg (by omega), if_pos h]
          simp [h1, h]
      · rw [readX _ (by omega), readY _ (by omega)] at e
        have h1 : decide (m + 1 - (k + 1) < Lx) = true := by simp; omega
        have h2 : decide (m + 1 - (k + 1) < Ly) = true := by simp; omega
        rw [h1, h2] at e
        refine Runs.of e (Or.inr ⟨hkpos, by omega, ?_⟩)
        have h3 : m + 1 - (k + 1) + 1 = m + 1 - k := by omega
        simp only [h3])
    (m + 1) (cmpState σ X Y G 0 1 0 0 0 0) (Or.inr ⟨by omega, le_rfl, by simp⟩)
  obtain ⟨τ1, e1, rfl⟩ := p1
  -- the cases of the lengths
  rcases Nat.lt_trichotomy Lx Ly with hlt | heq | hgt
  · -- `Lx < Ly`: `x < y`
    have hxy : x < y := lt_of_natBitLength_lt hlt
    have hf : fin1 = cmpState σ X Y G m 0 1 m m 1 := by rw [hfin1, if_neg (by omega), if_neg (by omega)]
    rw [hf] at e1
    have ed := WXExec.dec cap (G 1) (cmpState σ X Y G m 0 1 m m 1) (by simp; omega)
    rw [cmpState_D, cmpState_setD, Nat.sub_self] at ed
    have ek := clearK_exec cap σ X Y G m m m 1 (by omega)
    have er := rewind_exec cap σ X Y G hXY m 1 (by omega)
    rw [cmpState_zero σ X Y G hz 1] at er
    have E : WXExec cap (ltNat X Y G) (cmpState σ X Y G 0 0 0 0 0 0) _ _ :=
      WXExec.seq e0 (WXExec.seq e1 (WXExec.seq (WXExec.ifrT (by simp) (WXExec.seq ed ek)) er))
    rw [hσ0] at E
    refine WXExec.cast cap E (by simp [hxy]) ?_
    unfold ltNatCost; omega
  · -- `Lx = Ly`: the bits decide
    have hf : fin1 = cmpState σ X Y G m 0 0 m m 0 := by rw [hfin1, if_pos heq]
    rw [hf] at e1
    have hmL : m = Lx := by omega
    have ef := bothFwd_exec cap σ X Y G hXY m 0 0 m m 0 (by omega)
    have p2 := Runs.count (cap := cap) (K := G 2) (body := bitBody X Y G) 15 Lx
      (fun i τ => τ = cmpState σ X Y G (m + 1 + i) 0 0 (Lx - i) (m + 1 + i)
        (decide (x % 2 ^ i < y % 2 ^ i)).toNat) (by omega)
      (by
        rintro i hi τ rfl -
        rw [cmpState_setK]
        have e := bitBody_exec cap σ X Y G hXY (m + 1 + i) (Lx - i - 1) (m + 1 + i)
          (decide (x % 2 ^ i < y % 2 ^ i)) (by omega)
        have bx : readTapeBit (σ.st X) (σ.sh X + (m + 1 + i)) = x.testBit i := by
          rw [read_natWord σ X hX hXh _ (by omega), hmL]; exact natWord_getD_payload x i hi
        have byy : readTapeBit (σ.st Y) (σ.sh Y + (m + 1 + i)) = y.testBit i := by
          rw [read_natWord σ Y hY hYh _ (by omega), hmL, heq]; exact natWord_getD_payload y i (by omega)
        rw [bx, byy, ← lt_mod_succ] at e
        refine Runs.of e ⟨?_, by simp⟩
        have h3 : m + 1 + i + 1 = m + 1 + (i + 1) := by omega
        have h4 : Lx - i - 1 = Lx - (i + 1) := by omega
        rw [h3, h4])
      (cmpState σ X Y G (m + 1) 0 0 m (m + 1) 0) (by simp [hmL, Nat.mod_one]) (by simp [hmL])
    obtain ⟨τ2, e2, rfl, -⟩ := p2
    have hxmod : x % 2 ^ Lx = x := Nat.mod_eq_of_lt (lt_two_pow_natBitLength x)
    have hymod : y % 2 ^ Lx = y := by rw [heq]; exact Nat.mod_eq_of_lt (lt_two_pow_natBitLength y)
    rw [hxmod, hymod, Nat.sub_self] at e2
    have er := rewind_exec cap σ X Y G hXY (m + 1 + Lx) (decide (x < y)).toNat (by omega)
    rw [cmpState_zero σ X Y G hz] at er
    have E : WXExec cap (ltNat X Y G) (cmpState σ X Y G 0 0 0 0 0 0) _ _ :=
      WXExec.seq e0 (WXExec.seq e1 (WXExec.seq (WXExec.ifrF (by simp) (WXExec.seq ef e2)) er))
    rw [hσ0] at E
    refine WXExec.cast cap E rfl ?_
    unfold ltNatCost; omega
  · -- `Ly < Lx`: `y < x`
    have hxy : ¬ x < y := not_lt.mpr (lt_of_natBitLength_lt hgt).le
    have hf : fin1 = cmpState σ X Y G m 0 1 m m 0 := by rw [hfin1, if_neg (by omega), if_pos hgt]
    rw [hf] at e1
    have ed := WXExec.dec cap (G 1) (cmpState σ X Y G m 0 1 m m 0) (by simp; omega)
    rw [cmpState_D, cmpState_setD, Nat.sub_self] at ed
    have ek := clearK_exec cap σ X Y G m m m 0 (by omega)
    have er := rewind_exec cap σ X Y G hXY m 0 (by omega)
    rw [cmpState_zero σ X Y G hz 0] at er
    have E : WXExec cap (ltNat X Y G) (cmpState σ X Y G 0 0 0 0 0 0) _ _ :=
      WXExec.seq e0 (WXExec.seq e1 (WXExec.seq (WXExec.ifrT (by simp) (WXExec.seq ed ek)) er))
    rw [hσ0] at E
    refine WXExec.cast cap E (by simp [hxy]) ?_
    unfold ltNatCost; omega

end LtNatExec


/-! ## Signed comparison of two `intWord`s -/

/-- Both heads of `A`, `B` moved by `h`. -/
def mvState (σ : WState ns nr) (A B : Fin (ns + 1)) (h : ℕ) : WState ns nr :=
  ⟨Function.update (Function.update σ.sh A (σ.sh A + h)) B (σ.sh B + h), σ.st, σ.val, σ.cell⟩

/-- Both heads one cell right. -/
def fw2 (A B : Fin (ns + 1)) : WMX ns nr := .seq (WMX.fwd A) (WMX.fwd B)

/-- Both heads one cell left. -/
def bw2 (A B : Fin (ns + 1)) : WMX ns nr := .seq (WMX.bwd A) (WMX.bwd B)

/-- **The signed comparison** `R := [b < a]` of `intWord a` on `A` and `intWord b` on `B`: the sign of
`intWord z = natWord [z < 0] ++ natWord |z|` is its third cell; equal signs compare the magnitudes by `ltNat`. -/
def ltInt (A B : Fin (ns + 1)) (G : Fin 5 ↪ Fin nr) : WMX ns nr :=
  .seq (fw2 A B) (.seq (fw2 A B)
    (.seq (.ifs A (.ifs B (.seq (fw2 A B) (.seq (ltNat A B G) (bw2 A B))) WMX.skip)
                  (.ifs B (WMX.inc (G 4)) (.seq (fw2 A B) (.seq (ltNat B A G) (bw2 A B)))))
    (.seq (bw2 A B) (bw2 A B))))

/-- The cost bound of `ltInt` on two magnitudes of bit lengths `La`, `Lb`. -/
def ltIntCost (La Lb : ℕ) : ℕ := ltNatCost La Lb + 40

section LtInt

variable (cap : ℕ) (σ : WState ns nr) (A B : Fin (ns + 1)) (G : Fin 5 ↪ Fin nr)

theorem mvState_zero : mvState σ A B 0 = σ := by
  refine WState.eq ?_ rfl rfl rfl
  funext q; simp [mvState]

theorem mvState_setv (h : ℕ) (r : Fin nr) (v : ℕ) : (mvState σ A B h).setv r v = mvState (σ.setv r v) A B h := rfl

theorem mvState_shA (hAB : A ≠ B) (h : ℕ) : (mvState σ A B h).sh A = σ.sh A + h := by
  simp [mvState, Function.update_of_ne hAB]

theorem mvState_shB (h : ℕ) : (mvState σ A B h).sh B = σ.sh B + h := by simp [mvState]

theorem fw2_exec (hAB : A ≠ B) (h : ℕ) : WXExec cap (fw2 A B) (mvState σ A B h) (mvState σ A B (h + 1)) 3 := by
  have e1 := WXExec.fwd cap A (mvState σ A B h)
  have e2 := WXExec.fwd cap B ((mvState σ A B h).seth A ((mvState σ A B h).sh A + 1))
  refine WXExec.cast cap (WXExec.seq e1 e2) ?_ le_rfl
  refine WState.eq ?_ rfl rfl rfl
  funext q
  by_cases hqB : q = B
  · subst hqB; simp [mvState, Function.update_of_ne hAB.symm]; omega
  · by_cases hqA : q = A
    · subst hqA; simp [mvState, Function.update_of_ne hqB, hAB]; omega
    · simp [mvState, Function.update_of_ne hqB, Function.update_of_ne hqA]

theorem bw2_exec (hAB : A ≠ B) (h : ℕ) : WXExec cap (bw2 A B) (mvState σ A B (h + 1)) (mvState σ A B h) 3 := by
  have e1 := WXExec.bwd cap A (mvState σ A B (h + 1))
  have e2 := WXExec.bwd cap B ((mvState σ A B (h + 1)).seth A ((mvState σ A B (h + 1)).sh A - 1))
  refine WXExec.cast cap (WXExec.seq e1 e2) ?_ le_rfl
  refine WState.eq ?_ rfl rfl rfl
  funext q
  by_cases hqB : q = B
  · subst hqB; simp [mvState, Function.update_of_ne hAB.symm]
  · by_cases hqA : q = A
    · subst hqA; simp [mvState, Function.update_of_ne hqB, hAB]
    · simp [mvState, Function.update_of_ne hqB, Function.update_of_ne hqA]

theorem intWord_eq (z : ℤ) : NearCubicGates.Close.Interfaces.intWord z =
    [true, false, decide (z < 0)] ++ RepairRepresentation.natWord z.natAbs := by
  unfold NearCubicGates.Close.Interfaces.intWord
  congr 1
  split_ifs with h <;> simp [h] <;> decide

/-- **`ltInt` decides `b < a`.** From the heads at the starts of `intWord a` on `A` and `intWord b` on `B` and the
five registers at zero, `ltInt` sets `R` to `[b < a]` and leaves everything else as it was. -/
theorem ltInt_exec (hAB : A ≠ B) {pA rA pB rB : List Bool} (a b : ℤ)
    (hA : σ.st A = pA ++ NearCubicGates.Close.Interfaces.intWord a ++ rA) (hAh : σ.sh A = pA.length)
    (hB : σ.st B = pB ++ NearCubicGates.Close.Interfaces.intWord b ++ rB) (hBh : σ.sh B = pB.length)
    (hz : ∀ i, σ.val (G i) = 0)
    (hc : 2 * natBitLength a.natAbs + 2 * natBitLength b.natAbs + 4 ≤ cap) :
    WXExec cap (ltInt A B G) σ (σ.setv (G 4) (decide (b < a)).toNat)
      (ltIntCost (natBitLength a.natAbs) (natBitLength b.natAbs)) := by
  rw [intWord_eq] at hA hB
  have rdA : readTapeBit (σ.st A) (σ.sh A + 2) = decide (a < 0) := by
    rw [hA, hAh, List.append_assoc, read_pre]; simp [readTapeBit]
  have rdB : readTapeBit (σ.st B) (σ.sh B + 2) = decide (b < 0) := by
    rw [hB, hBh, List.append_assoc, read_pre]; simp [readTapeBit]
  -- the magnitudes, seen from the moved heads
  have mA : (mvState σ A B 3).st A = (pA ++ [true, false, decide (a < 0)]) ++
      RepairRepresentation.natWord a.natAbs ++ rA := by
    simp [mvState, hA, List.append_assoc]
  have mAh : (mvState σ A B 3).sh A = (pA ++ [true, false, decide (a < 0)]).length := by
    rw [mvState_shA σ A B hAB, hAh]; simp
  have mB : (mvState σ A B 3).st B = (pB ++ [true, false, decide (b < 0)]) ++
      RepairRepresentation.natWord b.natAbs ++ rB := by
    simp [mvState, hB, List.append_assoc]
  have mBh : (mvState σ A B 3).sh B = (pB ++ [true, false, decide (b < 0)]).length := by
    rw [mvState_shB, hBh]; simp
  have mz : ∀ i, (mvState σ A B 3).val (G i) = 0 := hz
  have f0 := fw2_exec cap σ A B hAB 0
  have f1 := fw2_exec cap σ A B hAB 1
  have f2 := fw2_exec cap σ A B hAB 2
  have g2 := fun (τ : WState ns nr) => bw2_exec cap τ A B hAB 2
  have g1 := fun (τ : WState ns nr) => bw2_exec cap τ A B hAB 1
  have g0 := fun (τ : WState ns nr) => bw2_exec cap τ A B hAB 0
  have wA : wbit (mvState σ A B 2) A = decide (a < 0) := by
    simp only [wbit, mvState_shA σ A B hAB]; exact rdA
  have wB : wbit (mvState σ A B 2) B = decide (b < 0) := by
    simp only [wbit, mvState_shB]; exact rdB
  have hn := hz 4
  rcases lt_or_ge a 0 with ha | ha <;> rcases lt_or_ge b 0 with hb | hb
  · -- both negative: `b < a ↔ |a| < |b|`
    have el := ltNat_exec cap (mvState σ A B 3) A B G hAB a.natAbs b.natAbs mA mAh mB mBh mz (by omega)
    rw [mvState_setv] at el
    have hv : decide (a.natAbs < b.natAbs) = decide (b < a) := by
      apply decide_eq_decide.mpr; omega
    rw [hv] at el
    have E : WXExec cap (ltInt A B G) (mvState σ A B 0) _ _ :=
      WXExec.seq f0 (WXExec.seq f1 (WXExec.seq (WXExec.ifsT (by rw [wA]; simp [ha])
        (WXExec.ifsT (by rw [wB]; simp [hb]) (WXExec.seq f2 (WXExec.seq el (g2 _)))))
        (WXExec.seq (g1 _) (g0 _))))
    rw [mvState_zero, mvState_zero] at E
    refine WXExec.cast cap E rfl ?_
    unfold ltIntCost ltNatCost; omega
  · -- `a < 0 ≤ b`: `b < a` is false
    have E : WXExec cap (ltInt A B G) (mvState σ A B 0) _ _ :=
      WXExec.seq f0 (WXExec.seq f1 (WXExec.seq (WXExec.ifsT (by rw [wA]; simp [ha])
        (WXExec.ifsF (by rw [wB]; simp; omega) (WXExec.skip cap _)))
        (WXExec.seq (g1 _) (g0 _))))
    rw [mvState_zero] at E
    have hv : decide (b < a) = false := by simp; omega
    refine WXExec.cast cap E ?_ ?_
    · rw [hv]; exact (BinW.setv_same hn).symm
    · unfold ltIntCost ltNatCost; omega
  · -- `b < 0 ≤ a`: `b < a` is true
    have ei := WXExec.inc cap (G 4) (mvState σ A B 2) (by simp only [mvState]; omega)
    have hset : (mvState σ A B 2).setv (G 4) ((mvState σ A B 2).val (G 4) + 1) =
        mvState (σ.setv (G 4) 1) A B 2 := by rw [mvState_setv]; simp [mvState, hn]
    rw [hset] at ei
    have E : WXExec cap (ltInt A B G) (mvState σ A B 0) _ _ :=
      WXExec.seq f0 (WXExec.seq f1 (WXExec.seq (WXExec.ifsF (by rw [wA]; simp; omega)
        (WXExec.ifsT (by rw [wB]; simp [hb]) ei))
        (WXExec.seq (bw2_exec cap (σ.setv (G 4) 1) A B hAB 1) (bw2_exec cap (σ.setv (G 4) 1) A B hAB 0))))
    rw [mvState_zero, mvState_zero] at E
    have hv : decide (b < a) = true := by simp; omega
    refine WXExec.cast cap E (by rw [hv]; rfl) ?_
    unfold ltIntCost ltNatCost; omega
  · -- both nonnegative: `b < a ↔ |b| < |a|`
    have el := ltNat_exec cap (mvState σ A B 3) B A G hAB.symm b.natAbs a.natAbs mB mBh mA mAh mz (by omega)
    rw [mvState_setv] at el
    have hv : decide (b.natAbs < a.natAbs) = decide (b < a) := by
      apply decide_eq_decide.mpr; omega
    rw [hv] at el
    have E : WXExec cap (ltInt A B G) (mvState σ A B 0) _ _ :=
      WXExec.seq f0 (WXExec.seq f1 (WXExec.seq (WXExec.ifsF (by rw [wA]; simp; omega)
        (WXExec.ifsF (by rw [wB]; simp; omega) (WXExec.seq f2 (WXExec.seq el (g2 _)))))
        (WXExec.seq (g1 _) (g0 _))))
    rw [mvState_zero, mvState_zero] at E
    refine WXExec.cast cap E rfl ?_
    unfold ltIntCost ltNatCost; omega

end LtInt

end NearQuarticWires.Control
