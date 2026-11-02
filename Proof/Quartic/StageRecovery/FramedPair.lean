import Proof.Quartic.StageGamma.Retain

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearQuarticWires.StageRecovery.FramedPair

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Codec
open NearCubicGates.Close.CounterMachine NearCubicGates.Close.Expand.PolyTab

variable {Request : Type} {input left right : Request → List Bool} {lb rb : Request → ℕ}

/-- `lem:print`, paper/paper.tex: the header call
uses a fresh physical bank after the preserved original source. -/
def lmap (t u : ℕ) (j : Fin t) : Fin (t + u + 4) := ⟨j.val + 1, by omega⟩

/-- `lem:print`, paper/paper.tex: the native table
call has a disjoint physical bank with its own actual source copy. -/
def rmap (t u : ℕ) (j : Fin u) : Fin (t + u + 4) := ⟨j.val + t + 1, by omega⟩

/-- `lem:print`, paper/paper.tex: the two real
call clocks and joined output occupy three distinct final tapes. -/
def rulerL (t u : ℕ) : Fin (t + u + 4) := ⟨t + u + 1, by omega⟩

/-- `lem:print`, paper/paper.tex: the second
callee has its own explicit once-only reset clock. -/
def rulerR (t u : ℕ) : Fin (t + u + 4) := ⟨t + u + 2, by omega⟩

/-- `lem:print`, paper/paper.tex: the joined
framed output lies outside both ordinary machine banks. -/
def out (t u : ℕ) : Fin (t + u + 4) := ⟨t + u + 3, by omega⟩

/-- `lem:print`, paper/paper.tex: the explicit
physical program copies its source twice, executes both real calls and
scans both computed frames exactly once into their ordered concatenation. -/
noncomputable def program
    (f : WordFunction Request input (fun r => frame (left r)) lb)
    (g : WordFunction Request input (fun r => frame (right r)) rb) :
    WMX (f.program.tapeCount + g.program.tapeCount + 3) 3 :=
  let t := f.program.tapeCount
  let u := g.program.tapeCount
  .seq (.wm (copyRW 0 (lmap t u (tape0 f.program)) 0 1 2))
    (.seq (.wm (copyRW 0 (rmap t u (tape0 g.program)) 0 1 2))
      (.seq (.machZ f.program.machine (lmap t u) (rulerL t u))
        (.seq (.machZ g.program.machine (rmap t u) (rulerR t u))
          (.seq (.wm (.whs (lmap t u f.program.outputTape)
            (copyPairW (lmap t u f.program.outputTape) (out t u) 0)))
            (.seq (.wm (.whs (rmap t u g.program.outputTape)
              (copyPairW (rmap t u g.program.outputTape) (out t u) 0)))
              (.wm (emitC (out t u) 0 false)))))))

/-- `prop:time`, paper/paper.tex: each actual
call and every source/output scan is paid once, with constant-factor
source copying independent of the table or support-family census. -/
def cost (r : Request) : ℕ :=
  2 * lb r + 2 * rb r + 300 * ((input r).length + (left r).length + (right r).length + 1)

/-- `prop:time`, paper/paper.tex: the pair
program's only initial workspace consists of its two real call clocks. -/
def lens (t u bl br : ℕ) (i : Fin (t + u + 4)) : ℕ :=
  if i.val = t + u + 1 then bl else if i.val = t + u + 2 then br else 0

/-- `prop:time`, paper/paper.tex: the actual
three-register copy/output capacity is linear in the literal input and
both computed output lengths, without changing either algorithm. -/
def capacity (r : Request) : ℕ :=
  4 * ((input r).length + (left r).length + (right r).length + 1) + 4

/-- `lem:print`, paper/paper.tex: disjoint real
cold calls compute the exact ordered header/native-packet concatenation
from the same original input, with no supplied callee outputs. -/
theorem run
    (f : WordFunction Request input (fun r => frame (left r)) lb)
    (g : WordFunction Request input (fun r => frame (right r)) rb) (r : Request) :
    Runs (capacity (input := input) (left := left) (right := right) r) (program f g)
      (idealStart (f.program.tapeCount + g.program.tapeCount + 3) 3 (input r)
        (lens f.program.tapeCount g.program.tapeCount (lb r) (rb r)))
      (cost (input := input) (left := left) (right := right) (lb := lb) (rb := rb) r)
      (fun b => b.st (out f.program.tapeCount g.program.tapeCount) = frame (left r ++ right r)) := by
  let t := f.program.tapeCount
  let u := g.program.tapeCount
  let cap := capacity (input := input) (left := left) (right := right) r
  let σ := idealStart (t + u + 3) 3 (input r) (lens t u (lb r) (rb r))
  have ht : 2 ≤ t := f.program.twoTapes
  have hu : 2 ≤ u := g.program.twoTapes
  have li : Function.Injective (lmap t u) := by
    intro i j h; apply Fin.ext; have := congrArg Fin.val h; simp only [lmap, Fin.val_mk] at this; omega
  have ri : Function.Injective (rmap t u) := by
    intro i j h; apply Fin.ext; have := congrArg Fin.val h; simp only [rmap, Fin.val_mk] at this; omega
  have lr (i : Fin t) (j : Fin u) : lmap t u i ≠ rmap t u j := by
    intro h; have := congrArg Fin.val h; have := i.isLt; simp only [lmap, rmap, Fin.val_mk] at *; omega
  have l0 (i : Fin t) : lmap t u i ≠ 0 := by
    intro h; have := congrArg Fin.val h; change i.val + 1 = 0 at this; omega
  have r0 (j : Fin u) : rmap t u j ≠ 0 := by
    intro h; have := congrArg Fin.val h; change j.val + t + 1 = 0 at this; omega
  have lf (i : Fin t) (k : ℕ) (hk : t + u ≤ k) (hl : k < t + u + 4) :
      lmap t u i ≠ (⟨k, hl⟩ : Fin (t + u + 4)) := by
    intro h; have := congrArg Fin.val h; have := i.isLt; simp only [lmap, Fin.val_mk] at *; omega
  have rf (j : Fin u) (k : ℕ) (hk : t + u + 1 ≤ k) (hl : k < t + u + 4) :
      rmap t u j ≠ (⟨k, hl⟩ : Fin (t + u + 4)) := by
    intro h; have := congrArg Fin.val h; have := j.isLt; simp only [rmap, Fin.val_mk] at *; omega
  have lo (i : Fin t) : lmap t u i ≠ out t u := lf i _ (by omega) (by omega)
  have ro (j : Fin u) : rmap t u j ≠ out t u := rf j _ (by omega) (by omega)
  have ll (i : Fin t) : lmap t u i ≠ rulerL t u := lf i _ (by omega) (by omega)
  have lg (i : Fin t) : lmap t u i ≠ rulerR t u := lf i _ (by omega) (by omega)
  have rl (j : Fin u) : rmap t u j ≠ rulerL t u := rf j _ (by omega) (by omega)
  have rg (j : Fin u) : rmap t u j ≠ rulerR t u := rf j _ (by omega) (by omega)
  have fl0 : rulerL t u ≠ 0 := by
    intro he; have hv := congrArg Fin.val he; change t + u + 1 = 0 at hv; omega
  have fr0 : rulerR t u ≠ 0 := by
    intro he; have hv := congrArg Fin.val he; change t + u + 2 = 0 at hv; omega
  have fo0 : out t u ≠ 0 := by
    intro he; have hv := congrArg Fin.val he; change t + u + 3 = 0 at hv; omega
  let L := lmap t u (tape0 f.program)
  let R := rmap t u (tape0 g.program)
  have σsrc : σ.st 0 = frame (input r) := by simp [σ, idealStart]
  have σblank (i : Fin (t + u + 4)) (hi : i ≠ 0)
      (hL : i.val ≠ t + u + 1) (hR : i.val ≠ t + u + 2) : σ.st i = [] := by
    simp [σ, idealStart, lens, hi, hL, hR]
  have lfar (i : Fin t) : (lmap t u i).val < t + u + 1 := by simp [lmap]; have := i.isLt; omega
  have rfar (j : Fin u) : (rmap t u j).val < t + u + 1 := by simp [rmap]; have := j.isLt; omega
  have eL := copyRW_spec cap (0 : Fin (t + u + 4)) L (l0 _).symm (0 : Fin 3) 1 2
    (by decide) (by decide) (by decide) (input r) [] σ (by simpa using σsrc) rfl
    (σblank L (l0 _) (by have := lfar (tape0 f.program); omega) (by have := lfar (tape0 f.program); omega))
    rfl rfl rfl rfl (by dsimp [cap, capacity]; omega)
  let s1 := σ.sets L (frame (input r))
  have eR := copyRW_spec cap (0 : Fin (t + u + 4)) R (r0 _).symm (0 : Fin 3) 1 2
    (by decide) (by decide) (by decide) (input r) [] s1
    (by simp only [s1, WState.sets_st, Function.update_of_ne (show (0 : Fin (t + u + 4)) ≠ L from (l0 _).symm), σsrc, List.append_nil]) rfl
    (by simp only [s1, WState.sets_st, Function.update_of_ne (show R ≠ L from (lr _ _).symm)]
        exact σblank R (r0 _) (by have := rfar (tape0 g.program); omega) (by have := rfar (tape0 g.program); omega))
    rfl rfl rfl rfl (by dsimp [cap, capacity]; omega)
  let s2 := s1.sets R (frame (input r))
  have fIn : s2.st (lmap t u (tape0 f.program)) = frame (input r) := by simp [s2, s1, L, R, lr]
  have fBlank : ∀ j, j ≠ tape0 f.program → s2.st (lmap t u j) = [] := by
    intro j hj
    have hjL : lmap t u j ≠ L := by intro he; exact hj (li he)
    change Function.update (Function.update σ.st L (frame (input r))) R (frame (input r))
      (lmap t u j) = []
    rw [Function.update_of_ne (show lmap t u j ≠ R from lr j (tape0 g.program)),
      Function.update_of_ne hjL]
    exact σblank (lmap t u j) (l0 j) (by have := lfar j; omega) (by have := lfar j; omega)
  have fClock : s2.st (rulerL t u) = List.replicate (lb r) false := by
    simp only [s2, s1, WState.sets_st, Function.update_of_ne (show rulerL t u ≠ R from (rl (tape0 g.program)).symm),
      Function.update_of_ne (show rulerL t u ≠ L from (ll (tape0 f.program)).symm)]
    simp [σ, idealStart, lens, fl0, rulerL]
  obtain ⟨s3, ef, fout, fheads, foff, fregs⟩ := wfDock_exact f r cap (lmap t u) li
    (rulerL t u) ll s2 fIn fBlank (fun _ => rfl)
    (lb r) fClock rfl le_rfl
  have gIn : s3.st (rmap t u (tape0 g.program)) = frame (input r) := by
    rw [(foff _ (fun j => lr j _)).1]
    simp [s2, R]
  have gBlank : ∀ j, j ≠ tape0 g.program → s3.st (rmap t u j) = [] := by
    intro j hj
    rw [(foff _ (fun i => lr i j)).1]
    have hjR : rmap t u j ≠ R := by intro he; exact hj (ri he)
    simp only [s2, s1, WState.sets_st, Function.update_of_ne hjR,
      Function.update_of_ne (show rmap t u j ≠ L from (lr (tape0 f.program) j).symm)]
    exact σblank (rmap t u j) (r0 j) (by have := rfar j; omega) (by have := rfar j; omega)
  have gH : ∀ j, s3.sh (rmap t u j) = 0 := by intro j; exact (foff _ (fun i => lr i j)).2
  have gClock : s3.st (rulerR t u) = List.replicate (rb r) false := by
    rw [(foff _ lg).1]
    simp only [s2, s1, WState.sets_st, Function.update_of_ne (show rulerR t u ≠ R from (rg (tape0 g.program)).symm),
      Function.update_of_ne (show rulerR t u ≠ L from (lg (tape0 f.program)).symm)]
    simp [σ, idealStart, lens, fr0, rulerR]
  have gClockH : s3.sh (rulerR t u) = 0 := (foff _ lg).2
  obtain ⟨s4, eg, gout, gheads, goff, gregs⟩ := wfDock_exact g r cap (rmap t u) ri
    (rulerR t u) rg s3 gIn gBlank gH
    (rb r) gClock gClockH le_rfl
  have hleft : s4.st (lmap t u f.program.outputTape) = frame (left r) := by
    rw [(goff _ (fun j => (lr _ j).symm)).1, fout]
  have hleftH : s4.sh (lmap t u f.program.outputTape) = 0 := by
    rw [(goff _ (fun j => (lr _ j).symm)).2, fheads]
  have hOut : s4.st (out t u) = [] := by
    rw [(goff _ ro).1, (foff _ lo).1]
    simp only [s2, s1, WState.sets_st, Function.update_of_ne (show out t u ≠ R from (ro (tape0 g.program)).symm),
      Function.update_of_ne (show out t u ≠ L from (lo (tape0 f.program)).symm)]
    simp [σ, idealStart, lens, fo0, out]
  have hOutH : s4.sh (out t u) = 0 := by
    rw [(goff _ ro).2, (foff _ lo).2]
    rfl
  have v0 : s4.val 0 = 0 := by rw [gregs, fregs]; rfl
  have hfirst := copyFrame_loop cap (lmap t u f.program.outputTape) (out t u)
    (lo _) (0 : Fin 3) [] (left r) [] s4 (by simpa using hleft) hleftH
    (by rw [hOutH, hOut]; rfl) (by rw [v0]; dsimp [cap, capacity]; omega)
  simp only [List.length_nil, Nat.zero_add] at hfirst
  let s5 := (appendO s4 (out t u) 0 (Streaming.marks (left r))).seth
    (lmap t u f.program.outputTape) (2 * (left r).length)
  have hright : s5.st (rmap t u g.program.outputTape) = frame (right r) := by
    simp [s5, appendO, (ro _), gout]
  have hrightH : s5.sh (rmap t u g.program.outputTape) = 0 := by
    simp [s5, appendO, (ro _), (lr _ _).symm, gheads]
  have h5Out : s5.st (out t u) = Streaming.marks (left r) := by simp [s5, appendO, hOut]
  have h5Head : s5.sh (out t u) = (s5.st (out t u)).length := by
    simp [s5, appendO, (lo _).symm, hOutH, hOut]
  have h5v : s5.val 0 = 2 * (left r).length := by simp [s5, appendO, v0, Streaming.marks_length]
  have hsecond := copyFrame_loop cap (rmap t u g.program.outputTape) (out t u)
    (ro _) (0 : Fin 3) [] (right r) [] s5 (by simpa using hright) hrightH h5Head
    (by rw [h5v]; dsimp [cap, capacity]; omega)
  simp only [List.length_nil, Nat.zero_add] at hsecond
  let s6 := (appendO s5 (out t u) 0 (Streaming.marks (right r))).seth
    (rmap t u g.program.outputTape) (2 * (right r).length)
  have h6Out : s6.st (out t u) = Streaming.marks (left r) ++ Streaming.marks (right r) := by
    simp [s6, appendO, h5Out]
  have h6Head : s6.sh (out t u) = (s6.st (out t u)).length := by
    simp [s6, appendO, (ro _).symm, h5Head, h5Out, List.length_append]
  have h6v : s6.val 0 < cap := by
    simp [s6, appendO, h5v, Streaming.marks_length]
    dsimp [cap, capacity]
    omega
  have eLast := emitC_spec cap (out t u) (0 : Fin 3) false s6 h6Head h6v
  refine ⟨appendO s6 (out t u) 0 [false], ?_, ?_⟩
  · have e := (WXExec.wm eL).seq ((WXExec.wm eR).seq (ef.seq (eg.seq
      ((WXExec.wm hfirst).seq ((WXExec.wm hsecond).seq (WXExec.wm eLast))))))
    exact e.mono (by dsimp [cost]; omega)
  · change (appendO s6 (out t u) 0 [false]).st (out t u) = frame (left r ++ right r)
    simp only [appendO, WState.setv_st, WState.seth_st, WState.sets_st,
      Function.update_self, h6Out]
    rw [frame_eq_marks, Streaming.marks_append]

/-- `lem:print`, paper/paper.tex: a genuine
ordinary cold word function returns both computed payloads in order,
with all actual calls, copies and cleanup included. -/
noncomputable def wordFunction
    (f : WordFunction Request input (fun r => frame (left r)) lb)
    (g : WordFunction Request input (fun r => frame (right r)) rb) :
    WordFunction Request input (fun r => frame (left r ++ right r))
      (fun r => 2 * cost (input := input) (left := left) (right := right) (lb := lb) (rb := rb) r + 2) :=
  wordFunction_of_ideal (program f g) (out f.program.tapeCount g.program.tapeCount)
    (by simp [out]) (capacity (input := input) (left := left) (right := right))
    (fun r => lens f.program.tapeCount g.program.tapeCount (lb r) (rb r))
    (cost (input := input) (left := left) (right := right) (lb := lb) (rb := rb))
    (fun _ => le_rfl) (by
      intro r
      exact ⟨by simp [lens, out], run f g r⟩)

end NearQuarticWires.StageRecovery.FramedPair
