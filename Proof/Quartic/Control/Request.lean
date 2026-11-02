import Proof.Quartic.Control.Walks
import Proof.Gates.Codec.Emit

/-!
# Writing the coefficient request of a walk

Paper: `cor:conditional`, paper/paper.tex, and Step 3: one coefficient `2^S c_π(w)` per
closed walk `w`, computed from the seed parameters, the prefix and the walk (`Machine.gammaRequestWord`:
`natWord ℓ ++ natWord kh ++ natWord Q ++ natWord |π| ++ natWord code ++ listWord natWord (slots of w)`).

The part before the slots is the same for all walks of a child evaluation; it is kept marked on a stream `HS`. The
slots come from the count fields of the walk index (`Control.emitSlots`). `writeRequest` writes the framed request
on an empty stream and brings every head back (`writeRequest_exec`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.Control

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.RepairOrdinary.Streaming (marks marks_length marks_append)
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat (appendO appendO_st appendO_sh appendO_val appendO_cell)

variable {ns nr : ℕ}

/-- **The request writer**: `frame (hw ++ natWord m ++ natWord d₁ ++ … ++ natWord d_m)` on `X`, from `marks hw` on
`HS` and the `m` count fields on `CT`. Registers: `OP`, `C` (counters), `LC` (a bound on the length of the
fields), `D` (scratch), `Y` (the number transcoder). -/
def writeRequest (m : ℕ) (HS CT X : Fin (ns + 1)) (OP C LC D : Fin nr) (Y : Fin 5 ↪ Fin nr) : WMX ns nr :=
  .seq (copyLoop false HS X OP C)
  (.seq (.wm (NearCubicGates.Close.Codec.rewindLoop HS C))
  (.seq (.wm (NearCubicGates.Close.Codec.emitMarks X OP (natWord m)))
  (.seq (.wm (emitSlots CT X Y OP m))
  (.seq (.wm (emitC X OP false))
  (.seq (.wm (WM.rewind X OP))
  (.seq (.wm (NearCubicGates.Close.Codec.dupR LC C D))
  (.wm (NearCubicGates.Close.Codec.rewindLoop CT C))))))))

/-- The cost bound of the request writer. -/
def requestCost (h m kh Lc : ℕ) : ℕ := 200 * (h + 1) + m * (3 * kh ^ 2 + 100 * kh + 81) + 60 * (m + 1) * (kh + 2) +
  30 * (Lc + 1) + 300


theorem natWord_length_bound (x : ℕ) : (natWord x).length ≤ 2 * x + 3 := by
  rw [NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_length]
  have := natBitLength_le_self_succ x; omega

/-- **The request.** From `marks hw` on `HS`, the count fields of `m` digits on `CT` and an empty `X` (heads and
counters at `0`, `LC` at least the length of the fields), `writeRequest` writes exactly
`frame (hw ++ natWord m ++ natWord d₁ ++ … ++ natWord d_m)` on `X` and changes nothing else. -/
theorem writeRequest_exec (cap : ℕ) (σ : WState ns nr) (m : ℕ) (HS CT X : Fin (ns + 1)) (OP C LC D : Fin nr)
    (Y : Fin 5 ↪ Fin nr) (hHX : HS ≠ X) (hCX : CT ≠ X) (hHC : HS ≠ CT) (hOC : OP ≠ C) (hOL : OP ≠ LC)
    (hOD : OP ≠ D) (hCL : C ≠ LC) (hCD : C ≠ D) (hLD : LC ≠ D) (hYO : ∀ i, Y i ≠ OP) (hYC : ∀ i, Y i ≠ C)
    (hw : List Bool) (ds : List ℕ) (kh Lc : ℕ) (hds : ∀ d ∈ ds, d < 2 ^ kh) (hm : ds.length = m)
    (hHS : σ.st HS = marks hw ++ [false]) (hHSh : σ.sh HS = 0) (hCT : σ.st CT = ds.flatMap (countField kh))
    (hCTh : σ.sh CT = 0) (hX : σ.st X = []) (hXh : σ.sh X = 0) (hOP : σ.val OP = 0) (hC : σ.val C = 0)
    (hLC : σ.val LC = Lc) (hD : σ.val D = 0) (hY : ∀ i, σ.val (Y i) = 0) (hLc : m * (2 * kh + 1) ≤ Lc)
    (hcap : 8 * hw.length + 8 * m + (m + 2) * (4 * kh + 8) + 2 * Lc + 40 ≤ cap) :
    WXExec cap (writeRequest m HS CT X OP C LC D Y) σ
      (σ.sets X (frame (hw ++ natWord m ++ ds.flatMap natWord))) (requestCost hw.length m kh Lc) := by
  subst hm
  -- copy the fixed part
  have e1 := copyLoop_exec cap σ HS X OP C false hHX hOC [] hw [false] (by simp [hHS]) (by simp [hHSh]) rfl
    (by rw [hX, hXh]; rfl) (by omega) (by omega)
  rw [bitCells_false] at e1
  set σ1 := copySt σ HS X OP C hw.length (marks hw) with hσ1
  have e2 := NearCubicGates.Close.Codec.rewindLoop_spec cap HS C (2 * hw.length) σ1 (by simp [hσ1, copySt, hC])
    (by simp [hσ1, copySt, Function.update_of_ne hHX, hHSh]) (by omega)
  set σ2 := (σ1.setv C 0).seth HS (σ1.sh HS - 2 * hw.length) with hσ2
  have h2X : σ2.st X = marks hw := by simp [hσ2, hσ1, copySt, hX]
  have h2Xh : σ2.sh X = (σ2.st X).length := by
    rw [h2X]; simp [hσ2, hσ1, copySt, Function.update_of_ne hHX.symm, hXh, marks_length]
  have h2OP : σ2.val OP = 2 * hw.length := by
    simp [hσ2, hσ1, copySt, Function.update_of_ne hOC, hOP, marks_length]
  -- the number of slots
  have hnl := natWord_length_bound ds.length
  have e3 := NearCubicGates.Close.Codec.emitMarks_spec cap X OP (natWord ds.length) σ2 h2Xh (by omega)
  set σ3 := appendO σ2 X OP (marks (natWord ds.length)) with hσ3
  -- the slots
  have h3CT : σ3.st CT = [] ++ ds.flatMap (countField kh) ++ [] := by
    simp [hσ3, hσ2, hσ1, copySt, Function.update_of_ne hCX, hCT]
  have h3CTh : σ3.sh CT = ([] : List Bool).length := by
    simp [hσ3, hσ2, hσ1, copySt, Function.update_of_ne hCX, Function.update_of_ne hHC.symm, hCTh]
  have h3Y : ∀ i, σ3.val (Y i) = 0 := by
    intro i; simp [hσ3, hσ2, hσ1, copySt, Function.update_of_ne (hYO i), Function.update_of_ne (hYC i), hY i]
  have h3Xh : σ3.sh X = (σ3.st X).length := by simp [hσ3, h2Xh]
  have h3OP : σ3.val OP = 2 * hw.length + 2 * (natWord ds.length).length := by
    simp [hσ3, h2OP, marks_length]
  have hk : kh + 1 ≤ cap := by nlinarith
  have e4 := emitSlots_exec cap CT X Y OP hCX hYO kh [] hk ds [] σ3 hds h3CT h3CTh h3Y h3Xh
    (by rw [h3OP]; nlinarith)
  set σ4 := appendO (σ3.seth CT (([] : List Bool).length + ds.length * (2 * kh + 1))) X OP
    (marks (ds.flatMap natWord)) with hσ4
  -- the end of the frame
  have h4Xh : σ4.sh X = (σ4.st X).length := by
    simp [hσ4, Function.update_of_ne hCX.symm, h3Xh]
  have hsl : (ds.flatMap natWord).length ≤ ds.length * (2 * kh + 3) := by
    have := sum_map_le ds (fun d => (natWord d).length) (fun _ => 2 * kh + 3)
      (fun d hd => natWord_length_le_field kh d (hds d hd))
    rw [List.length_flatMap]; simpa using this
  have h4OP : σ4.val OP = 2 * hw.length + 2 * (natWord ds.length).length + 2 * (ds.flatMap natWord).length := by
    simp [hσ4, h3OP, marks_length]
  have e5 := emitC_spec cap X OP false σ4 h4Xh (by rw [h4OP]; nlinarith)
  set σ5 := ((σ4.sets X (σ4.st X ++ [false])).seth X (σ4.sh X + 1)).setv OP (σ4.val OP + 1) with hσ5
  have h5X : σ5.st X = marks hw ++ marks (natWord ds.length) ++ marks (ds.flatMap natWord) ++ [false] := by
    simp [hσ5, hσ4, hσ3, Function.update_of_ne hCX.symm, h2X]
  have h4eq : σ4.sh X = σ4.val OP := by
    rw [h4Xh, h4OP]; simp [hσ4, hσ3, Function.update_of_ne hCX.symm, h2X, marks_length]; ring
  have h5OP : σ5.val OP = σ5.sh X := by simp [hσ5, h4eq]
  have h5v : σ5.val OP = σ4.val OP + 1 := by simp [hσ5]
  have e6 := wrewind_spec cap X OP (σ5.val OP) σ5 rfl (by
    rw [h5v, h4OP]
    have : 2 * (ds.flatMap natWord).length ≤ (ds.length + 2) * (4 * kh + 8) := by nlinarith
    omega)
  set σ6 := (σ5.setv OP 0).seth X (σ5.sh X - σ5.val OP) with hσ6
  -- the counter back to its first cell
  have h6C : σ6.val C = 0 := by
    simp [hσ6, hσ5, hσ4, hσ3, hσ2, Function.update_of_ne hOC.symm]
  have h6LC : σ6.val LC = Lc := by
    simp [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, copySt, Function.update_of_ne hOL.symm, Function.update_of_ne hCL.symm,
      hLC]
  have h6D : σ6.val D = 0 := by
    simp [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, copySt, Function.update_of_ne hOD.symm, Function.update_of_ne hCD.symm,
      hD]
  have e7 := NearCubicGates.Close.Codec.dupR_spec cap LC C D hCL.symm hLD hCD σ6 h6D (by rw [h6LC, h6C]; omega)
  rw [h6C, h6LC, Nat.zero_add] at e7
  have e8 := rewindLoop_sat cap CT C Lc (σ6.setv C Lc) (by simp) (by omega)
  refine WXExec.mono (WXExec.cast cap (WXExec.seq e1 (WXExec.seq (WXExec.wm e2) (WXExec.seq (WXExec.wm e3)
    (WXExec.seq (WXExec.wm e4) (WXExec.seq (WXExec.wm e5) (WXExec.seq (WXExec.wm e6) (WXExec.seq (WXExec.wm e7)
    (WXExec.wm e8)))))))) ?_ le_rfl) ?_
  · have hfr : frame (hw ++ natWord ds.length ++ ds.flatMap natWord) =
        marks hw ++ marks (natWord ds.length) ++ marks (ds.flatMap natWord) ++ [false] := by
      rw [NearCubicGates.Close.Codec.frame_eq_marks]; simp [marks_append, List.append_assoc]
    have h4CT : σ4.sh CT = ds.length * (2 * kh + 1) := by simp [hσ4, Function.update_of_ne hCX]
    refine WState.eq ?_ ?_ ?_ rfl
    · funext q
      by_cases hqX : q = X
      · rw [hqX]
        simp only [WState.seth_sh, WState.setv_sh, Function.update_of_ne hCX.symm, WState.sets_sh]
        rw [show σ6.sh X = 0 by simp [hσ6, h5OP]]; rw [hXh]
      · by_cases hqC : q = CT
        · rw [hqC]
          simp only [WState.seth_sh, WState.setv_sh, Function.update_self, WState.sets_sh]
          have : σ6.sh CT = ds.length * (2 * kh + 1) := by
            simp [hσ6, hσ5, Function.update_of_ne hCX, h4CT]
          rw [this, hCTh]; omega
        · by_cases hqH : q = HS
          · rw [hqH]
            simp [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, copySt, Function.update_apply, hHC, hHX, hHSh]
          · simp [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, copySt, Function.update_of_ne hqC, Function.update_of_ne hqX,
              Function.update_of_ne hqH]
    · funext q
      by_cases hqX : q = X
      · rw [hqX]
        have h6X : σ6.st X = σ5.st X := by simp [hσ6]
        simp only [WState.seth_st, WState.setv_st, WState.sets_st, Function.update_self, Function.update_of_ne hCX.symm]
        rw [h6X, h5X, hfr]
      · by_cases hqH : q = HS
        · rw [hqH]
          simp [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, copySt, Function.update_of_ne hHX]
        · simp [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, copySt, Function.update_of_ne hqX, Function.update_of_ne hqH]
    · funext r
      by_cases hrC : r = C
      · rw [hrC]; simp [hC]
      · by_cases hrO : r = OP
        · rw [hrO]; simp [Function.update_of_ne hOC, hσ6, hOP]
        · simp [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, copySt, Function.update_of_ne hrC, Function.update_of_ne hrO]
  · unfold requestCost
    rw [h5v, h4OP]
    nlinarith [hsl, hnl]


/-! ## Appending a coefficient to the table -/

/-- Move the head of `O` back by half the value of `P`, `P := 0`. -/
def halfRewind (O : Fin (ns + 1)) (P : Fin nr) : WM ns nr := .whr P (.seq (.dec P) (.seq (.dec P) (.bwd O)))

theorem halfRewind_spec (cap : ℕ) (O : Fin (ns + 1)) (P : Fin nr) :
    ∀ (k : ℕ) (σ : WState ns nr), σ.val P = 2 * k → 2 * k ≤ cap →
      WExec cap (halfRewind O P) σ ((σ.setv P 0).seth O (σ.sh O - k)) (k * 7 + 1)
  | 0, σ, h0, _ => by
    refine WExec.cast cap (WExec.whrF (by simpa using h0)) ?_ le_rfl
    refine WState.eq ?_ rfl ?_ rfl
    · funext q; by_cases hq : q = O
      · subst hq; simp
      · simp [Function.update_of_ne hq]
    · funext q; by_cases hq : q = P
      · subst hq; simp [h0]
      · simp [Function.update_of_ne hq]
  | k + 1, σ, hk, hc => by
    have e1 := WExec.dec (cap := cap) P σ (by rw [hk]; omega)
    have e2 := WExec.dec (cap := cap) P (σ.setv P (σ.val P - 1)) (by simp; rw [hk]; omega)
    set σ2 := (σ.setv P (σ.val P - 1)).setv P ((σ.setv P (σ.val P - 1)).val P - 1) with hσ2
    have e3 := WExec.bwd (cap := cap) O σ2
    have e4 := halfRewind_spec cap O P k (σ2.seth O (σ2.sh O - 1)) (by simp [hσ2, hk]; omega) (by omega)
    refine WExec.mono (WExec.cast cap (WExec.whrT (by omega) (WExec.seq e1 (WExec.seq e2 e3)) e4) ?_ le_rfl)
      (by ring_nf; omega)
    refine WState.eq ?_ rfl ?_ rfl
    · funext q; by_cases hq : q = O
      · subst hq; simp [hσ2]; omega
      · simp [hσ2, Function.update_of_ne hq]
    · funext q; by_cases hq : q = P
      · subst hq; simp [hσ2]
      · simp [hσ2, Function.update_of_ne hq]

/-- **Append a coefficient**: copy the integer `intWord z` (raw, on `O` from its head) to the table `T` as marks,
then bring the head of `O` back. `R 7` counts the cells written. -/
def appendGamma (O T : Fin (ns + 1)) (R : Fin 8 ↪ Fin nr) : WM ns nr :=
  .seq (NearCubicGates.Close.WorkerArith.copyK O T R 2) (halfRewind O (R 7))

theorem intWord_flatMap (z : ℤ) : NearCubicGates.Close.Interfaces.intWord z =
    [if z < 0 then 1 else 0, z.natAbs].flatMap natWord := by
  simp [NearCubicGates.Close.Interfaces.intWord]

/-- **The coefficient is appended.** From `intWord z` on `O` (head `0`), the head of `T` at its end and the counters
`R 1`, `R 2`, `R 7` at zero, `appendGamma` appends `marks (intWord z)` to `T` and leaves everything else as it was. -/
theorem appendGamma_exec (cap : ℕ) (σ : WState ns nr) (O T : Fin (ns + 1)) (hOT : O ≠ T) (R : Fin 8 ↪ Fin nr)
    (z : ℤ) (rest : List Bool) (hO : σ.st O = NearCubicGates.Close.Interfaces.intWord z ++ rest) (hOh : σ.sh O = 0)
    (hT : σ.sh T = (σ.st T).length) (h1 : σ.val (R 1) = 0) (h2 : σ.val (R 2) = 0) (h7 : σ.val (R 7) = 0)
    (hc : 2 * (NearCubicGates.Close.Interfaces.intWord z).length + 2 ≤ cap) :
    WExec cap (appendGamma O T R) σ
      ((appendO σ T (R 7) (marks (NearCubicGates.Close.Interfaces.intWord z))).setv (R 7) 0)
      (130 * (NearCubicGates.Close.Interfaces.intWord z).length + 2) := by
  rw [intWord_flatMap] at hO hc ⊢
  have e1 := NearCubicGates.Close.WorkerArith.copyKM cap O T hOT R [if z < 0 then 1 else 0, z.natAbs] σ [] rest
    (by rw [hO]; rfl) (by simp [hOh]) hT h1 h2 (by rw [h7]; omega)
  simp only [List.length_nil, Nat.zero_add] at e1
  have e2 := halfRewind_spec cap O (R 7) ([if z < 0 then 1 else 0, z.natAbs].flatMap natWord).length
    ((appendO σ T (R 7) (marks ([if z < 0 then 1 else 0, z.natAbs].flatMap natWord))).seth O
      ([if z < 0 then 1 else 0, z.natAbs].flatMap natWord).length) (by simp [h7, marks_length]; ring) (by omega)
  refine WExec.mono (WExec.cast cap (WExec.seq e1 e2) ?_ le_rfl) (by omega)
  refine WState.eq ?_ rfl rfl rfl
  funext q; by_cases hq : q = O
  · subst hq; simp [Function.update_of_ne hOT, hOh]
  · simp [Function.update_of_ne hq]


/-! ## The next walk -/

/-- `F := F + m`. -/
def incTimes (F : Fin nr) : ℕ → WMX ns nr
  | 0 => WMX.skip
  | m + 1 => .seq (WMX.inc F) (incTimes F m)

theorem incTimes_exec (cap : ℕ) (F : Fin nr) : ∀ (m : ℕ) (σ : WState ns nr), σ.val F + m ≤ cap →
    WXExec cap (incTimes F m) σ (σ.setv F (σ.val F + m)) (4 * m)
  | 0, σ, _ => by
    refine WXExec.cast cap (WXExec.skip cap σ) ?_ le_rfl
    exact (BinW.setv_same (by simp)).symm
  | m + 1, σ, hc => by
    have e1 := WXExec.inc cap F σ (by omega)
    have e2 := incTimes_exec cap F m (σ.setv F (σ.val F + 1)) (by simp; omega)
    refine WXExec.mono (WXExec.cast cap (WXExec.seq e1 e2) ?_ le_rfl) (by omega)
    refine WState.eq rfl rfl ?_ rfl
    funext q; by_cases hq : q = F
    · subst hq; simp; omega
    · simp [Function.update_of_ne hq]

/-- **The next walk**: carry `1` through the `m` count fields of the walk index on `CT`, then rewind `CT` (by the
bound `LC`). The carry out stays in `Z 0`. -/
def incWalk (m : ℕ) (CT : Fin (ns + 1)) (Z : Fin 5 ↪ Fin nr) (LC C D : Fin nr) : WMX ns nr :=
  .seq (WMX.inc (Z 0)) (.seq (incTimes (Z 4) m) (.seq (fieldsLoop CT Z)
    (.seq (.wm (NearCubicGates.Close.Codec.dupR LC C D)) (.wm (NearCubicGates.Close.Codec.rewindLoop CT C)))))

/-- **The next walk.** From the count fields of the digits `ds` on `CT` (head `0`), the carry, field and counter
registers at zero, `Z 3 = kh`, `LC = Lc` at least the length of the fields: `incWalk` writes the count fields of
`(digitsInc kh ds true).1`, sets the carry register to the carry out and restores everything else. -/
theorem incWalk_exec (cap : ℕ) (σ : WState ns nr) (CT : Fin (ns + 1)) (Z : Fin 5 ↪ Fin nr) (LC C D : Fin nr)
    (hZL : ∀ i, Z i ≠ LC) (hZC : ∀ i, Z i ≠ C) (hZD : ∀ i, Z i ≠ D) (hCL : C ≠ LC) (hCD : C ≠ D) (hLD : LC ≠ D)
    (kh Lc : ℕ) (ds : List ℕ) (hds : ∀ d ∈ ds, d < 2 ^ kh) (rest : List Bool)
    (hCT : σ.st CT = ds.flatMap (countField kh) ++ rest) (hCTh : σ.sh CT = 0)
    (h0 : σ.val (Z 0) = 0) (h1 : σ.val (Z 1) = 0) (h2 : σ.val (Z 2) = 0) (h3 : σ.val (Z 3) = kh)
    (h4 : σ.val (Z 4) = 0) (hC : σ.val C = 0) (hD : σ.val D = 0) (hLC : σ.val LC = Lc)
    (hLc : ds.length * (2 * kh + 1) ≤ Lc) (hcap : 2 * kh + 2 * ds.length + Lc + 4 ≤ cap) :
    WXExec cap (incWalk ds.length CT Z LC C D) σ
      ((σ.sets CT ((digitsInc kh ds true).1.flatMap (countField kh) ++ rest)).setv (Z 0)
        (digitsInc kh ds true).2.toNat)
      (5 + 4 * ds.length + (ds.length * (60 * kh + 25) + 1) + 18 * Lc + 3 + 5 * Lc + 1 + 4) := by
  have e1 := WXExec.inc cap (Z 0) σ (by omega)
  rw [h0] at e1
  have e2 := incTimes_exec cap (Z 4) ds.length (σ.setv (Z 0) (0 + 1))
    (by simp [Function.update_of_ne (Z_ne Z (show (4 : Fin 5) ≠ 0 by decide)), h4]; omega)
  have hstart : (σ.setv (Z 0) (0 + 1)).setv (Z 4) ((σ.setv (Z 0) (0 + 1)).val (Z 4) + ds.length) =
      fSt σ CT Z ([] ++ ds.flatMap (countField kh) ++ rest) ([] : List Bool).length ds.length (true : Bool).toNat := by
    refine WState.eq ?_ ?_ ?_ rfl
    · funext q; by_cases hq : q = CT
      · subst hq; simp [fSt, bitsSt, hCTh]
      · simp [fSt, bitsSt, Function.update_of_ne hq]
    · funext q; by_cases hq : q = CT
      · subst hq; simp [fSt, bitsSt, hCT]
      · simp [fSt, bitsSt, Function.update_of_ne hq]
    · funext q
      simp only [fSt, bitsSt, WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all [Z_ne Z (show (4 : Fin 5) ≠ 0 by decide)]
  rw [hstart] at e2
  have e3 := fieldsLoop_exec cap CT Z σ kh h3 h2 rest (by omega) ds [] true hds (by omega)
  set σ3 := fSt σ CT Z ([] ++ (digitsInc kh ds true).1.flatMap (countField kh) ++ rest)
    (([] : List Bool).length + ds.length * (2 * kh + 1)) 0 (digitsInc kh ds true).2.toNat with hσ3
  have h3LC : σ3.val LC = Lc := by
    simp [hσ3, fSt, bitsSt, Function.update_of_ne (hZL 0).symm, Function.update_of_ne (hZL 1).symm,
      Function.update_of_ne (hZL 4).symm, hLC]
  have h3C : σ3.val C = 0 := by
    simp [hσ3, fSt, bitsSt, Function.update_of_ne (hZC 0).symm, Function.update_of_ne (hZC 1).symm,
      Function.update_of_ne (hZC 4).symm, hC]
  have h3D : σ3.val D = 0 := by
    simp [hσ3, fSt, bitsSt, Function.update_of_ne (hZD 0).symm, Function.update_of_ne (hZD 1).symm,
      Function.update_of_ne (hZD 4).symm, hD]
  have e4 := NearCubicGates.Close.Codec.dupR_spec cap LC C D hCL.symm hLD hCD σ3 h3D (by rw [h3LC, h3C]; omega)
  rw [h3C, h3LC, Nat.zero_add] at e4
  have e5 := rewindLoop_sat cap CT C Lc (σ3.setv C Lc) (by simp) (by omega)
  refine WXExec.mono (WXExec.cast cap (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq (WXExec.wm e4)
    (WXExec.wm e5))))) ?_ le_rfl) (by omega)
  refine WState.eq ?_ ?_ ?_ rfl
  · funext q; by_cases hq : q = CT
    · subst hq; simp [hσ3, fSt, bitsSt, hCTh]; omega
    · simp [hσ3, fSt, bitsSt, Function.update_of_ne hq]
  · funext q; by_cases hq : q = CT
    · subst hq; simp [hσ3, fSt, bitsSt]
    · simp [hσ3, fSt, bitsSt, Function.update_of_ne hq]
  · funext q
    by_cases hqC : q = C
    · subst hqC
      simp [hσ3, fSt, bitsSt, Function.update_of_ne (hZC 0).symm, hC]
    · simp only [hσ3, fSt, bitsSt, WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all [Z_ne Z (show (4 : Fin 5) ≠ 0 by decide),
        Z_ne Z (show (1 : Fin 5) ≠ 0 by decide), Z_ne Z (show (4 : Fin 5) ≠ 1 by decide)]

end NearQuarticWires.Control
