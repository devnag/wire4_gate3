import Proof.Quartic.Control.Compare
import Proof.Gates.Codec.PairFrame

/-!
# Writing the input word of a child evaluation

Paper: Step 3 of `sec:algorithm`, paper/paper.tex: a child evaluation of the prefix `π` and the
bit `b` reads the word after Step 2 and the prefix `πb` (`Greedy.childInput`: `certWord ++ frame (π ++ [b])`).

The program writes, on an empty stream `X`, the framed child input `frame (w ++ frame (π ++ [b]))`, from the framed
word `frame w` on a stream `IN` and the marked prefix `marks π` on a stream `P`. Framing is cell-pair marking:
`frame u = marks u ++ [0]`, `marks u` the bits of `u`, each after a marker `1` (`Codec.frame_eq_marks`). So the
framed child input is `marks w`, then `marks (marks π)` (each bit `y` of `π` as `1, 1, 1, y`), then `1, 1, 1, b`,
then `1, 0` and `0` (`childFrame_eq`).

* `copyLoop`: append the marked bits of a marked word, each bit `y` written as `1, y` (or as `1, 1, 1, y` when
  doubling), counting the cells read (`copyLoop_exec`);
* `writeChild`: the whole input word, all heads and counters back at `0` (`writeChild_exec`), in time linear in
  `|w| + |π|`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.Control

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat (appendO emitPair emitPair_spec appendO_st appendO_sh
  appendO_val appendO_cell)
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (read_pre)
open NearCubicWires.RepairOrdinary.Streaming (marks marks_append marks_length)

variable {ns nr : ℕ}

/-! ## Words -/

/-- The cells appended for one bit `y`: `1, y`, or `1, 1, 1, y` when doubling. -/
def bitCells (dbl : Bool) (y : Bool) : List Bool := (if dbl then [true, true] else []) ++ [true, y]

theorem bitCells_false (U : List Bool) : U.flatMap (bitCells false) = marks U := by
  unfold marks; congr 1

theorem bitCells_true (U : List Bool) : U.flatMap (bitCells true) = marks (marks U) := by
  induction U with
  | nil => rfl
  | cons y U ih =>
    simp [List.flatMap_cons, ih, bitCells, marks]

/-- **The framed child input** as cells. -/
theorem childFrame_eq (w π : List Bool) (b : Bool) :
    frame (w ++ frame (π ++ [b])) =
      marks w ++ marks (marks π) ++ [true, true, true, b] ++ [true, false] ++ [false] := by
  rw [NearCubicGates.Close.Codec.frame_eq_marks, NearCubicGates.Close.Codec.frame_eq_marks]
  simp [marks, List.append_assoc]

theorem marks_split (U rest : List Bool) (k : ℕ) (hk : k < U.length) :
    marks U ++ rest = marks (U.take k) ++ (true :: U[k] :: (marks (U.drop (k + 1)) ++ rest)) := by
  have hU : U = U.take k ++ U[k] :: U.drop (k + 1) := by
    conv_lhs => rw [← List.take_append_drop k U]
    rw [List.drop_eq_getElem_cons hk]
  calc marks U ++ rest = marks (U.take k ++ U[k] :: U.drop (k + 1)) ++ rest := by rw [← hU]
    _ = _ := by
      rw [marks_append]
      simp only [marks, List.flatMap_cons, List.cons_append, List.nil_append, List.append_assoc]

theorem read_marks_mark (U rest : List Bool) (k : ℕ) (hk : k < U.length) :
    readTapeBit (marks U ++ rest) (2 * k) = true := by
  rw [marks_split U rest k hk]
  have h : (marks (U.take k)).length = 2 * k := by simp [marks_length]; omega
  rw [← h, show (marks (U.take k)).length = (marks (U.take k)).length + 0 by rfl, read_pre]
  rfl

theorem read_marks_bit (U rest : List Bool) (k : ℕ) (hk : k < U.length) :
    readTapeBit (marks U ++ rest) (2 * k + 1) = U[k] := by
  rw [marks_split U rest k hk]
  have h : (marks (U.take k)).length = 2 * k := by simp [marks_length]; omega
  rw [← h, read_pre]
  rfl

theorem read_marks_end (U rest : List Bool) (hrest : readTapeBit rest 0 = false) :
    readTapeBit (marks U ++ rest) (2 * U.length) = false := by
  have h : (marks U).length = 2 * U.length := marks_length U
  rw [← h, show (marks U).length = (marks U).length + 0 by rfl, read_pre]
  exact hrest

/-! ## The copy loop -/

/-- The prefix emitted before each bit: nothing, or `1, 1` when doubling. -/
def preEmit (dbl : Bool) (X : Fin (ns + 1)) (OP : Fin nr) : WMX ns nr :=
  if dbl then .wm (emitPair X OP true) else WMX.skip

/-- Append the bits of the marked word on `S`, each as `bitCells dbl`, to `X` (`OP` counts the cells of `X`);
`C` counts the cells read on `S`. -/
def copyLoop (dbl : Bool) (S X : Fin (ns + 1)) (OP C : Fin nr) : WMX ns nr :=
  .whs S (.seq (WMX.fwd S) (.seq (preEmit dbl X OP) (.seq (.wm (NearCubicGates.Close.Codec.emitScanned S X OP))
    (.seq (WMX.fwd S) (.seq (WMX.inc C) (WMX.inc C))))))

/-- The state after copying `k` bits, the word `w` appended. -/
def copySt (σ : WState ns nr) (S X : Fin (ns + 1)) (OP C : Fin nr) (k : ℕ) (w : List Bool) : WState ns nr :=
  ⟨Function.update (Function.update σ.sh S (σ.sh S + 2 * k)) X (σ.sh X + w.length),
    Function.update σ.st X (σ.st X ++ w),
    Function.update (Function.update σ.val OP (σ.val OP + w.length)) C (σ.val C + 2 * k), σ.cell⟩

theorem copySt_zero (σ : WState ns nr) (S X : Fin (ns + 1)) (OP C : Fin nr) : copySt σ S X OP C 0 [] = σ := by
  refine WState.eq ?_ ?_ ?_ rfl <;> funext q <;> simp [copySt]

section Copy

variable (cap : ℕ) (σ : WState ns nr) (S X : Fin (ns + 1)) (OP C : Fin nr)

theorem copyBody_exec (dbl : Bool) (hSX : S ≠ X) (hOC : OP ≠ C) (k : ℕ) (w : List Bool) (y : Bool)
    (hy : readTapeBit (σ.st S) (σ.sh S + 2 * k + 1) = y) (hX : σ.sh X = (σ.st X).length)
    (hc : σ.val OP + w.length + 4 ≤ cap) (hc' : σ.val C + 2 * k + 2 ≤ cap) :
    WXExec cap (.seq (WMX.fwd S) (.seq (preEmit dbl X OP) (.seq (.wm (NearCubicGates.Close.Codec.emitScanned S X OP))
      (.seq (WMX.fwd S) (.seq (WMX.inc C) (WMX.inc C))))))
      (copySt σ S X OP C k w) (copySt σ S X OP C (k + 1) (w ++ bitCells dbl y)) 50 := by
  set τ0 := copySt σ S X OP C k w with hτ0
  have hXne : X ≠ S := hSX.symm
  have e1 := WXExec.fwd cap S τ0
  set τ1 := τ0.seth S (τ0.sh S + 1) with hτ1
  have hτ1X : τ1.sh X = (τ1.st X).length := by
    simp [hτ1, hτ0, copySt, Function.update_of_ne hXne, hX]
  -- the prefix
  set v : List Bool := if dbl then [true, true] else [] with hv
  have e2 : WXExec cap (preEmit dbl X OP) τ1 (appendO τ1 X OP v) 16 := by
    cases dbl
    · simp only [preEmit, hv]
      refine WXExec.mono (WXExec.cast cap (WXExec.skip cap τ1) ?_ le_rfl) (by omega)
      exact (NearCubicGates.Close.Codec.appendO_nil τ1 X OP hτ1X).symm
    · simp only [preEmit, hv]
      refine WXExec.mono (WXExec.wm (emitPair_spec cap X OP true τ1 hτ1X ?_)) (by omega)
      simp [hτ1, hτ0, copySt, Function.update_of_ne hOC]
      omega
  set τ2 := appendO τ1 X OP v with hτ2
  have hτ2X : τ2.sh X = (τ2.st X).length := by
    simp [hτ2, hτ1X]
  have hb : wbit τ2 S = y := by
    simp [wbit, hτ2, hτ1, hτ0, copySt, Function.update_of_ne hSX, Function.update_of_ne hXne]
    rw [← hy]
  have hvl : v.length ≤ 2 := by rw [hv]; split <;> simp
  have e3 := NearCubicGates.Close.Codec.emitScanned_spec cap S X OP τ2 hτ2X (by
    simp [hτ2, hτ1, hτ0, copySt, Function.update_of_ne hOC]; omega)
  rw [hb] at e3
  set τ3 := appendO τ2 X OP (marks [y]) with hτ3
  have e4 := WXExec.fwd cap S τ3
  set τ4 := τ3.seth S (τ3.sh S + 1) with hτ4
  have e5 := WXExec.inc cap C τ4 (by simp [hτ4, hτ3, hτ2, hτ1, hτ0, copySt, Function.update_of_ne hOC.symm]; omega)
  set τ5 := τ4.setv C (τ4.val C + 1) with hτ5
  have e6 := WXExec.inc cap C τ5 (by simp [hτ5, hτ4, hτ3, hτ2, hτ1, hτ0, copySt, Function.update_of_ne hOC.symm]; omega)
  refine WXExec.mono (WXExec.cast cap (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq (WXExec.wm e3)
    (WXExec.seq e4 (WXExec.seq e5 e6))))) ?_ le_rfl) (by omega)
  have hcells : v ++ marks [y] = bitCells dbl y := by cases dbl <;> simp [hv, bitCells, marks]
  refine WState.eq ?_ ?_ ?_ rfl
  · funext q
    by_cases hqS : q = S
    · subst hqS; simp [hτ5, hτ4, hτ3, hτ2, hτ1, hτ0, copySt, Function.update_of_ne hSX]; omega
    · by_cases hqX : q = X
      · subst hqX
        simp [hτ5, hτ4, hτ3, hτ2, hτ1, hτ0, copySt, Function.update_of_ne hXne, ← hcells]; omega
      · simp [hτ5, hτ4, hτ3, hτ2, hτ1, hτ0, copySt, Function.update_of_ne hqS, Function.update_of_ne hqX]
  · funext q
    by_cases hqX : q = X
    · subst hqX; simp [hτ5, hτ4, hτ3, hτ2, hτ1, hτ0, copySt, ← hcells, List.append_assoc]
    · simp [hτ5, hτ4, hτ3, hτ2, hτ1, hτ0, copySt, Function.update_of_ne hqX]
  · funext q
    by_cases hqC : q = C
    · subst hqC; simp [hτ5, hτ4, hτ3, hτ2, hτ1, hτ0, copySt, Function.update_of_ne hOC.symm]; omega
    · by_cases hqO : q = OP
      · subst hqO; simp [hτ5, hτ4, hτ3, hτ2, hτ1, hτ0, copySt, hOC, ← hcells]; omega
      · simp [hτ5, hτ4, hτ3, hτ2, hτ1, hτ0, copySt, Function.update_of_ne hqC, Function.update_of_ne hqO]

/-- **The copy loop, on a stream that reads like a marked word.** If the stream `S` reads, from its head on, like
`marks U` followed by a `0`, the loop appends `U.flatMap (bitCells dbl)` to `X`, moves the head of `S` past
`marks U`, and adds `2|U|` to `C`. -/
theorem copyLoop_exec_read (dbl : Bool) (hSX : S ≠ X) (hOC : OP ≠ C) (U rest : List Bool)
    (hread : ∀ q, readTapeBit (σ.st S) (σ.sh S + q) = readTapeBit (marks U ++ rest) q)
    (hrest : readTapeBit rest 0 = false)
    (hX : σ.sh X = (σ.st X).length) (hc : σ.val OP + 4 * U.length + 4 ≤ cap)
    (hc' : σ.val C + 2 * U.length + 2 ≤ cap) :
    WXExec cap (copyLoop dbl S X OP C) σ (copySt σ S X OP C U.length (U.flatMap (bitCells dbl)))
      (U.length * 52 + 1) := by
  have hlen : ∀ k, (List.flatMap (bitCells dbl) (U.take k)).length ≤ 4 * k := by
    intro k
    induction k generalizing U with
    | zero => simp
    | succ k ih =>
      cases U with
      | nil => simp
      | cons y U => simp only [List.take_succ_cons, List.flatMap_cons, List.length_append]
                    have := ih U; cases dbl <;> simp [bitCells] <;> omega
  have key : ∀ m k, k + m = U.length →
      WXExec cap (copyLoop dbl S X OP C) (copySt σ S X OP C k ((U.take k).flatMap (bitCells dbl)))
        (copySt σ S X OP C U.length (U.flatMap (bitCells dbl))) (m * 52 + 1) := by
    intro m
    induction m with
    | zero =>
      intro k hk
      have hk' : k = U.length := by omega
      subst hk'
      rw [List.take_length]
      refine WXExec.mono (WXExec.whsF ?_) (by omega)
      simp only [wbit, copySt, Function.update_of_ne hSX.symm, Function.update_self, Function.update_of_ne hSX]
      rw [hread]
      exact read_marks_end U rest hrest
    | succ m ih =>
      intro k hk
      have hkU : k < U.length := by omega
      have hb : wbit (copySt σ S X OP C k ((U.take k).flatMap (bitCells dbl))) S = true := by
        simp only [wbit, copySt, Function.update_of_ne hSX.symm, Function.update_self, Function.update_of_ne hSX]
        rw [hread]
        exact read_marks_mark U rest k hkU
      have hy : readTapeBit (σ.st S) (σ.sh S + 2 * k + 1) = U[k] := by
        rw [Nat.add_assoc, hread]
        exact read_marks_bit U rest k hkU
      have e := copyBody_exec cap σ S X OP C dbl hSX hOC k ((U.take k).flatMap (bitCells dbl)) U[k] hy hX
        (by have := hlen k; omega) (by omega)
      have htake : (U.take k).flatMap (bitCells dbl) ++ bitCells dbl U[k] =
          (U.take (k + 1)).flatMap (bitCells dbl) := by
        rw [List.take_succ_eq_append_getElem hkU, List.flatMap_append]; simp
      rw [htake] at e
      have e2 := ih (k + 1) (by omega)
      exact WXExec.mono (WXExec.whsT hb e e2) (by ring_nf; omega)
  have := key U.length 0 (by omega)
  simpa [copySt_zero] using this

/-- **The copy loop.** From the head of `S` at the start of `marks U` (followed by a `0`), the loop appends
`U.flatMap (bitCells dbl)` to `X`, moves the head of `S` past `marks U`, and adds `2|U|` to `C`. -/
theorem copyLoop_exec (dbl : Bool) (hSX : S ≠ X) (hOC : OP ≠ C) (pS U rest : List Bool)
    (hS : σ.st S = pS ++ marks U ++ rest) (hSh : σ.sh S = pS.length) (hrest : readTapeBit rest 0 = false)
    (hX : σ.sh X = (σ.st X).length) (hc : σ.val OP + 4 * U.length + 4 ≤ cap)
    (hc' : σ.val C + 2 * U.length + 2 ≤ cap) :
    WXExec cap (copyLoop dbl S X OP C) σ (copySt σ S X OP C U.length (U.flatMap (bitCells dbl)))
      (U.length * 52 + 1) :=
  copyLoop_exec_read cap σ S X OP C dbl hSX hOC U rest
    (fun q => by rw [hS, hSh, List.append_assoc, read_pre]) hrest hX hc hc'

end Copy


/-! ## The child input -/

/-- **The child input writer**: `frame (w ++ frame (π ++ [b]))` on the empty stream `X`, from `frame w` on `IN` and
`marks π` on `P`. -/
def writeChild (b : Bool) (IN P X : Fin (ns + 1)) (OP C : Fin nr) : WMX ns nr :=
  .seq (copyLoop false IN X OP C)
  (.seq (.wm (NearCubicGates.Close.Codec.rewindLoop IN C))
  (.seq (copyLoop true P X OP C)
  (.seq (.wm (NearCubicGates.Close.Codec.rewindLoop P C))
  (.seq (.wm (emitPair X OP true))
  (.seq (.wm (emitPair X OP b))
  (.seq (.wm (emitPair X OP false))
  (.seq (.wm (emitC X OP false))
  (.wm (WM.rewind X OP)))))))))

/-- The cost bound of the writer. -/
def writeCost (w p : ℕ) : ℕ := 100 * (w + p + 2)

/-- **The writer.** From `frame w` on `IN`, `marks π` on `P` and an empty `X`, all heads and both counters at `0`,
`writeChild b` writes `frame (w ++ frame (π ++ [b]))` on `X` and restores every head and counter. -/
theorem writeChild_exec (cap : ℕ) (σ : WState ns nr) (b : Bool) (IN P X : Fin (ns + 1)) (OP C : Fin nr)
    (hIP : IN ≠ P) (hIX : IN ≠ X) (hPX : P ≠ X) (hOC : OP ≠ C) (w π : List Bool)
    (hIN : σ.st IN = frame w) (hINh : σ.sh IN = 0) (hP : σ.st P = marks π) (hPh : σ.sh P = 0)
    (hX : σ.st X = []) (hXh : σ.sh X = 0) (hO : σ.val OP = 0) (hC : σ.val C = 0)
    (hc : 4 * w.length + 4 * π.length + 20 ≤ cap) :
    WXExec cap (writeChild b IN P X OP C) σ (σ.sets X (frame (w ++ frame (π ++ [b])))) (writeCost w.length π.length) := by
  have hXP := hPX.symm
  have hXI := hIX.symm
  have hPI := hIP.symm
  -- copy `marks w`
  have e1 := copyLoop_exec cap σ IN X OP C false hIX hOC [] w [false]
    (by rw [hIN, NearCubicGates.Close.Codec.frame_eq_marks]; simp) (by simp [hINh]) (by rfl)
    (by rw [hX, hXh]; rfl) (by omega) (by omega)
  rw [bitCells_false] at e1
  set σ1 := copySt σ IN X OP C w.length (marks w) with hσ1
  have e2 := NearCubicGates.Close.Codec.rewindLoop_spec cap IN C (2 * w.length) σ1
    (by simp [hσ1, copySt, hC]) (by simp [hσ1, copySt, Function.update_of_ne hIX, hINh]) (by omega)
  set σ2 := (σ1.setv C 0).seth IN (σ1.sh IN - 2 * w.length) with hσ2
  -- copy `marks (marks π)`
  have e3 := copyLoop_exec cap σ2 P X OP C true hPX hOC [] π []
    (by simp [hσ2, hσ1, copySt, Function.update_of_ne hPX, hP]) (by simp [hσ2, hσ1, copySt,
      Function.update_of_ne hPX, Function.update_of_ne hPI, hPh]) (by rfl)
    (by simp [hσ2, hσ1, copySt, Function.update_of_ne hXI, hX, hXh, marks_length])
    (by simp [hσ2, hσ1, copySt, Function.update_of_ne hOC, hO]; omega)
    (by simp [hσ2, hσ1, copySt]; omega)
  rw [bitCells_true] at e3
  set σ3 := copySt σ2 P X OP C π.length (marks (marks π)) with hσ3
  have e4 := NearCubicGates.Close.Codec.rewindLoop_spec cap P C (2 * π.length) σ3
    (by simp [hσ3, hσ2, hσ1, copySt]) (by simp [hσ3, hσ2, hσ1, copySt, Function.update_of_ne hPX,
      Function.update_of_ne hPI, hPh]) (by omega)
  set σ4 := (σ3.setv C 0).seth P (σ3.sh P - 2 * π.length) with hσ4
  -- the tail cells
  have hX4 : σ4.st X = marks w ++ marks (marks π) := by
    simp [hσ4, hσ3, hσ2, hσ1, copySt, hX]
  have hX4h : σ4.sh X = (σ4.st X).length := by
    rw [hX4]; simp [hσ4, hσ3, hσ2, hσ1, copySt, Function.update_of_ne hXP, Function.update_of_ne hXI, hXh,
      marks_length]
  have hO4 : σ4.val OP = 2 * w.length + 4 * π.length := by
    simp [hσ4, hσ3, hσ2, hσ1, copySt, Function.update_of_ne hOC, hO, marks_length]; omega
  have e5 := emitPair_spec cap X OP true σ4 hX4h (by omega)
  set σ5 := appendO σ4 X OP [true, true] with hσ5
  have e6 := emitPair_spec cap X OP b σ5 (by simp [hσ5, hX4h]) (by simp [hσ5, hO4]; omega)
  set σ6 := appendO σ5 X OP [true, b] with hσ6
  have e7 := emitPair_spec cap X OP false σ6 (by simp [hσ6, hσ5, hX4h]) (by simp [hσ6, hσ5, hO4]; omega)
  set σ7 := appendO σ6 X OP [true, false] with hσ7
  have e8 := emitC_spec cap X OP false σ7 (by simp [hσ7, hσ6, hσ5, hX4h]) (by simp [hσ7, hσ6, hσ5, hO4]; omega)
  set σ8 := ((σ7.sets X (σ7.st X ++ [false])).seth X (σ7.sh X + 1)).setv OP (σ7.val OP + 1) with hσ8
  have hO8 : σ8.val OP = 2 * w.length + 4 * π.length + 7 := by
    simp [hσ8, hσ7, hσ6, hσ5, hO4]
  have e9 := wrewind_spec cap X OP (2 * w.length + 4 * π.length + 7) σ8 hO8 (by omega)
  refine WXExec.mono (WXExec.cast cap (WXExec.seq e1 (WXExec.seq (WXExec.wm e2) (WXExec.seq e3
    (WXExec.seq (WXExec.wm e4) (WXExec.seq (WXExec.wm e5) (WXExec.seq (WXExec.wm e6) (WXExec.seq (WXExec.wm e7)
    (WXExec.seq (WXExec.wm e8) (WXExec.wm e9))))))))) ?_ le_rfl) ?_
  · have hlen4 : σ4.sh X = 2 * w.length + 4 * π.length := by rw [hX4h, hX4]; simp [marks_length]; ring
    refine WState.eq ?_ ?_ ?_ rfl
    · funext q
      by_cases hqX : q = X
      · subst hqX
        simp only [hσ8, hσ7, hσ6, hσ5, WState.seth_sh, WState.setv_sh, WState.sets_sh, appendO_sh,
          Function.update_self]
        rw [hlen4]; simp [hXh]
      · simp only [hσ8, hσ7, hσ6, hσ5, WState.seth_sh, WState.setv_sh, WState.sets_sh, appendO_sh,
          Function.update_of_ne hqX]
        by_cases hqP : q = P
        · subst hqP
          simp [hσ4, hσ3, hσ2, hσ1, copySt, Function.update_of_ne hPX, Function.update_of_ne hPI, hPh]
        · by_cases hqI : q = IN
          · subst hqI
            simp [hσ4, hσ3, hσ2, hσ1, copySt, Function.update_of_ne hIX, Function.update_of_ne hIP, hINh]
          · simp [hσ4, hσ3, hσ2, hσ1, copySt, Function.update_of_ne hqX, Function.update_of_ne hqP,
              Function.update_of_ne hqI]
    · funext q
      by_cases hqX : q = X
      · subst hqX
        simp only [hσ8, hσ7, hσ6, hσ5, WState.seth_st, WState.setv_st, WState.sets_st, appendO_st,
          Function.update_self, hX4, childFrame_eq]
        simp [List.append_assoc]
      · simp [hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, copySt, Function.update_of_ne hqX]
    · funext q
      by_cases hqO : q = OP
      · subst hqO; simp [hσ8, hO]
      · by_cases hqC : q = C
        · subst hqC
          simp [hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, copySt, Function.update_of_ne hOC.symm, hC]
        · simp [hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, copySt, Function.update_of_ne hqO,
            Function.update_of_ne hqC]
  · unfold writeCost; omega

end NearQuarticWires.Control
