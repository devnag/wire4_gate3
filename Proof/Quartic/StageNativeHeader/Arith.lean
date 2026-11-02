import Proof.Quartic.StageNativeHeader.Regs

/-!
# Register arithmetic of the native header printer

Paper: `lem:print`, paper/paper.tex.

From the parameters `r, s` and the dense width read from the column field, the printer computes the row dimension
`d = width − (r/2) s` (`dRow_eq`), the stride `2·width + 2` of a cut, the signed record width `q = d + 2p + 3` and
`U = 2^d`, by counted loops (`whr_exec`) of additions (`ParseNat.addTo`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageNativeHeader

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (addTo addTo_spec)
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared

variable {ns nr : ℕ} (cap : ℕ)

/-- Only the registers of `L` change. -/
structure ROnly (σ τ : WState ns nr) (L : List (Fin nr)) : Prop where
  st : τ.st = σ.st
  sh : τ.sh = σ.sh
  cell : τ.cell = σ.cell
  val : ∀ x, x ∉ L → τ.val x = σ.val x

theorem ROnly.refl (σ : WState ns nr) (L : List (Fin nr)) : ROnly σ σ L := ⟨rfl, rfl, rfl, fun _ _ => rfl⟩

theorem ROnly.trans {σ τ ρ : WState ns nr} {L : List (Fin nr)} (h1 : ROnly σ τ L) (h2 : ROnly τ ρ L) :
    ROnly σ ρ L :=
  ⟨h2.st.trans h1.st, h2.sh.trans h1.sh, h2.cell.trans h1.cell, fun x hx => (h2.val x hx).trans (h1.val x hx)⟩

theorem ROnly.weaken {σ τ : WState ns nr} {L L' : List (Fin nr)} (h : ROnly σ τ L) (hL : ∀ x ∈ L, x ∈ L') :
    ROnly σ τ L' := ⟨h.st, h.sh, h.cell, fun x hx => h.val x (fun h' => hx (hL x h'))⟩

theorem ROnly.setv (σ : WState ns nr) {L : List (Fin nr)} {x : Fin nr} (hx : x ∈ L) (v : ℕ) :
    ROnly σ (σ.setv x v) L :=
  ⟨rfl, rfl, rfl, fun y hy => by
    have : y ≠ x := fun e => hy (e ▸ hx)
    simp [Function.update_of_ne this]⟩

/-- **A counted loop**: the body takes the state `S i` to `S (i+1)` while the register is not `0`. -/
theorem whr_exec (K : Fin nr) (P : WM ns nr) (c : ℕ) (S : ℕ → WState ns nr) (m : ℕ)
    (hnz : ∀ i < m, (S i).val K ≠ 0) (hz : (S m).val K = 0)
    (hP : ∀ i < m, WExec cap P (S i) (S (i + 1)) c) :
    WExec cap (.whr K P) (S 0) (S m) (m * (c + 2) + 1) := by
  have key : ∀ j, j ≤ m → WExec cap (.whr K P) (S (m - j)) (S m) (j * (c + 2) + 1) := by
    intro j
    induction j with
    | zero => intro _; simpa using WExec.whrF (cap := cap) (P := P) hz
    | succ j ih =>
      intro hj
      have e1 := hP (m - (j + 1)) (by omega)
      have e2 := ih (by omega)
      rw [show m - (j + 1) + 1 = m - j by omega] at e1
      exact WExec.mono (WExec.whrT (hnz (m - (j + 1)) (by omega)) e1 e2) (by ring_nf; omega)
  simpa using key m le_rfl

/-! ## `(r/2)·s` -/

/-- `rM += (r/2)·s` by `r/2` additions of `s`. -/
def halfMulP : WM ns hnr := .seq (addTo rR rK1 rTmp) (.whr rK1 (.seq (.dec rK1) (.seq (.dec rK1) (addTo rS rM rTmp))))

theorem halfMul_exec (σ : WState ns hnr) (r s : ℕ) (hr : σ.val rR = r) (hev : r % 2 = 0) (hs : σ.val rS = s)
    (hK : σ.val rK1 = 0) (hM : σ.val rM = 0) (hT : σ.val rTmp = 0) (hcap : r + r / 2 * s + s ≤ cap) :
    ∃ τ, WExec cap halfMulP σ τ (18 * r + r / 2 * (18 * s + 9) + 5) ∧ ROnly σ τ [rK1, rM] ∧
      τ.val rM = r / 2 * s ∧ τ.val rK1 = 0 := by
  have e1 := addTo_spec cap rR rK1 rTmp (by decide) (by decide) (by decide) σ hT (by omega) (by omega)
  set m := r / 2 with hm
  have hr2 : r = 2 * m := by omega
  let S : ℕ → WState ns hnr := fun i => (σ.setv rK1 (r - 2 * i)).setv rM (i * s)
  have vK : ∀ i, (S i).val rK1 = r - 2 * i := fun i => by simp [S, rK1, rM]
  have vM : ∀ i, (S i).val rM = i * s := fun i => by simp [S]
  have vO : ∀ i x, x ≠ rK1 → x ≠ rM → (S i).val x = σ.val x := fun i x h1 h2 => by
    simp [S, Function.update_of_ne h1, Function.update_of_ne h2]
  have hS0 : σ.setv rK1 (σ.val rK1 + σ.val rR) = S 0 := by
    refine WState.eq rfl rfl ?_ rfl
    funext x
    by_cases h1 : x = rK1
    · subst h1; rw [vK]; simp [hK, hr]
    · by_cases h2 : x = rM
      · subst h2; rw [vM]; simp [Function.update_of_ne h1, hM]
      · rw [vO 0 x h1 h2]; simp [Function.update_of_ne h1]
  rw [hS0] at e1
  have step : ∀ i < m, WExec cap (.seq (.dec rK1) (.seq (.dec rK1) (addTo rS rM rTmp))) (S i) (S (i + 1))
      (18 * s + 7) := by
    intro i hi
    have d1 := WExec.dec (cap := cap) rK1 (S i) (by have := vK i; omega)
    set A := (S i).setv rK1 ((S i).val rK1 - 1) with hA
    have d2 := WExec.dec (cap := cap) rK1 A (by simp [hA]; have := vK i; omega)
    set B := A.setv rK1 (A.val rK1 - 1) with hB
    have bK : B.val rK1 = r - 2 * (i + 1) := by simp [hB, hA, vK]; omega
    have bO : ∀ x, x ≠ rK1 → B.val x = (S i).val x := fun x h => by
      simp [hB, hA, Function.update_of_ne h]
    have d3 := addTo_spec cap rS rM rTmp (by decide) (by decide) (by decide) B
      (by rw [bO rTmp (by decide), vO i rTmp (by decide) (by decide), hT])
      (by rw [bO rS (by decide), vO i rS (by decide) (by decide), hs]; omega)
      (by rw [bO rM (by decide), bO rS (by decide), vO i rS (by decide) (by decide), vM, hs]; nlinarith)
    refine WExec.mono (WExec.cast cap (WExec.seq d1 (WExec.seq d2 d3)) ?_ le_rfl) (by
      rw [bO rS (by decide), vO i rS (by decide) (by decide), hs]; omega)
    refine WState.eq rfl rfl ?_ rfl
    funext x
    by_cases h1 : x = rM
    · subst h1
      rw [vM]; simp only [WState.setv_val, Function.update_self]
      rw [bO rM (by decide), bO rS (by decide), vO i rS (by decide) (by decide), vM, hs]; ring
    · by_cases h2 : x = rK1
      · subst h2
        rw [vK]; simp only [WState.setv_val, Function.update_of_ne h1]; exact bK
      · rw [vO (i + 1) x h2 h1]; simp only [WState.setv_val, Function.update_of_ne h1]
        rw [bO x h2, vO i x h2 h1]
  have e2 := whr_exec cap rK1 _ (18 * s + 7) S m (fun i hi => by rw [vK]; omega) (by rw [vK]; omega) step
  refine ⟨S m, WExec.mono (WExec.seq e1 e2) (by rw [hr] at *; ring_nf; omega), ?_, vM m, by rw [vK]; omega⟩
  refine ⟨rfl, rfl, rfl, fun x hx => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
  exact vO m x hx.1 hx.2

/-! ## `d = width − (r/2)·s` -/

theorem s_le_b (P : StarParams) : P.s ≤ P.b := by
  have h := P.b_succ
  have : P.s < 2 ^ P.s := Nat.lt_two_pow_self
  omega

/-- **The row dimension** from the dense width. -/
theorem dRow_eq (P : StarParams) :
    PrimT.C4Geo.dRow P = PrimT.C4Geo.width P - P.r / 2 * P.s ∧ P.r / 2 * P.s ≤ PrimT.C4Geo.width P := by
  have h := s_le_b P
  have e : P.r / 2 * (P.b - P.s) = P.r / 2 * P.b - P.r / 2 * P.s := Nat.mul_sub _ _ _
  have l : P.r / 2 * P.s ≤ P.r / 2 * P.b := Nat.mul_le_mul_left _ h
  unfold PrimT.C4Geo.dRow PrimT.C4Geo.width StarParams.leftCenterBits PrimT.C4Geo.hL
  omega

/-- `rD := rW − rM`. -/
def subP : WM ns hnr :=
  .seq (addTo rW rD rTmp) (.seq (addTo rM rK1 rTmp) (.whr rK1 (.seq (.dec rK1) (.dec rD))))

theorem sub_exec (σ : WState ns hnr) (w m : ℕ) (hw : σ.val rW = w) (hm : σ.val rM = m)
    (hD : σ.val rD = 0) (hK : σ.val rK1 = 0) (hT : σ.val rTmp = 0) (hcap : w + m + 1 ≤ cap) :
    ∃ τ, WExec cap subP σ τ (18 * w + 23 * m + 10) ∧ ROnly σ τ [rD, rK1] ∧ τ.val rD = w - m ∧
      τ.val rK1 = 0 := by
  have e1 := addTo_spec cap rW rD rTmp (by decide) (by decide) (by decide) σ hT (by omega) (by omega)
  set σ1 := σ.setv rD (σ.val rD + σ.val rW) with hσ1
  have e2 := addTo_spec cap rM rK1 rTmp (by decide) (by decide) (by decide) σ1
    (by simp [hσ1, Function.update_of_ne (show (rTmp : Fin hnr) ≠ rD by decide), hT])
    (by simp [hσ1, Function.update_of_ne (show (rM : Fin hnr) ≠ rD by decide), hm]; omega)
    (by simp [hσ1, Function.update_of_ne (show (rM : Fin hnr) ≠ rD by decide),
      Function.update_of_ne (show (rK1 : Fin hnr) ≠ rD by decide), hm, hK]; omega)
  let S : ℕ → WState ns hnr := fun i => (σ.setv rD (w - i)).setv rK1 (m - i)
  have vD : ∀ i, (S i).val rD = w - i := fun i => by simp [S, rK1, rD]
  have vK : ∀ i, (S i).val rK1 = m - i := fun i => by simp [S]
  have vO : ∀ i x, x ≠ rD → x ≠ rK1 → (S i).val x = σ.val x := fun i x h1 h2 => by
    simp [S, Function.update_of_ne h1, Function.update_of_ne h2]
  have hS0 : σ1.setv rK1 (σ1.val rK1 + σ1.val rM) = S 0 := by
    refine WState.eq rfl rfl ?_ rfl
    funext x
    by_cases h1 : x = rK1
    · subst h1; rw [vK]; simp [hσ1, Function.update_of_ne (show (rM : Fin hnr) ≠ rD by decide),
        Function.update_of_ne (show (rK1 : Fin hnr) ≠ rD by decide), hK, hm]
    · by_cases h2 : x = rD
      · subst h2; rw [vD]; simp [hσ1, Function.update_of_ne h1, hD, hw]
      · rw [vO 0 x h2 h1]; simp [hσ1, Function.update_of_ne h1, Function.update_of_ne h2]
  rw [hS0] at e2
  have step : ∀ i < m, WExec cap (.seq (.dec rK1) (.dec rD)) (S i) (S (i + 1)) 3 := by
    intro i hi
    have d1 := WExec.dec (cap := cap) rK1 (S i) (by have := vK i; omega)
    have d2 := WExec.dec (cap := cap) rD ((S i).setv rK1 ((S i).val rK1 - 1)) (by
      simp [Function.update_of_ne (show (rD : Fin hnr) ≠ rK1 by decide)]; have := vD i; omega)
    refine WExec.cast cap (WExec.seq d1 d2) ?_ (by omega)
    refine WState.eq rfl rfl ?_ rfl
    funext x
    by_cases h1 : x = rK1
    · subst h1; rw [vK]; simp [Function.update_of_ne (show (rK1 : Fin hnr) ≠ rD by decide), vK]; omega
    · by_cases h2 : x = rD
      · subst h2; rw [vD]; simp [Function.update_of_ne h1, vD]; omega
      · rw [vO (i + 1) x h2 h1]; simp [Function.update_of_ne h1, Function.update_of_ne h2, vO i x h2 h1]
  have e3 := whr_exec cap rK1 _ 3 S m (fun i hi => by rw [vK]; omega) (by rw [vK]; omega) step
  refine ⟨S m, WExec.mono (WExec.seq e1 (WExec.seq e2 e3)) (by
    simp only [hσ1, WState.setv_val, Function.update_of_ne (show (rM : Fin hnr) ≠ rD by decide), hw, hm]; omega), ?_,
    vD m, by rw [vK]; omega⟩
  refine ⟨rfl, rfl, rfl, fun x hx => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
  exact vO m x hx.1 hx.2

/-- `rT2 := 2·rW + 2`. -/
def strideP : WM ns hnr := .seq (addTo rW rT2 rTmp) (.seq (addTo rW rT2 rTmp) (.seq (.inc rT2) (.inc rT2)))

theorem stride_exec (σ : WState ns hnr) (w : ℕ) (hw : σ.val rW = w) (h0 : σ.val rT2 = 0) (hT : σ.val rTmp = 0)
    (hcap : 2 * w + 3 ≤ cap) :
    WExec cap strideP σ (σ.setv rT2 (2 * w + 2)) (36 * w + 15) := by
  have e1 := addTo_spec cap rW rT2 rTmp (by decide) (by decide) (by decide) σ hT (by omega) (by omega)
  rw [h0, hw, Nat.zero_add] at e1
  have e2 := addTo_spec cap rW rT2 rTmp (by decide) (by decide) (by decide) (σ.setv rT2 w)
    (by simp [Function.update_of_ne (show (rTmp : Fin hnr) ≠ rT2 by decide), hT])
    (by simp [Function.update_of_ne (show (rW : Fin hnr) ≠ rT2 by decide), hw]; omega)
    (by simp [Function.update_of_ne (show (rW : Fin hnr) ≠ rT2 by decide), hw]; omega)
  simp only [WState.setv_val, Function.update_self, Function.update_of_ne (show (rW : Fin hnr) ≠ rT2 by decide),
    hw, wsetv_setv] at e2
  have e3 := WExec.inc (cap := cap) rT2 (σ.setv rT2 (w + w)) (by simp; omega)
  have e4 := WExec.inc (cap := cap) rT2 ((σ.setv rT2 (w + w)).setv rT2 ((σ.setv rT2 (w + w)).val rT2 + 1))
    (by simp; omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4))) ?_ (by omega)
  simp only [WState.setv_val, Function.update_self, wsetv_setv]
  congr 1; omega

end NearQuarticWires.StageNativeHeader
