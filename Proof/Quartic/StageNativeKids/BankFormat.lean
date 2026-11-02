import Proof.Quartic.StageNativeKids.NaturalField
import Proof.Quartic.StageNativeKids.PoolRequest

set_option autoImplicit false

namespace NearQuarticWires.StageNativeKids

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.CopyNat
open NearCubicGates.Close NearCubicGates.Close.WordPrograms
open StageTuple

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: the
actual computed bank register writes its own marked dispatch bit. -/
def emitBankPair (flag OP : Fin nr) (dst : Fin (ns + 1)) : WM ns nr :=
  .ifr flag (emitPair dst OP true) (emitPair dst OP false)

/-- `lem:print`, paper/paper.tex: both
physical bank branches emit exactly their actual Boolean tag and
preserve every other tape and register. -/
theorem emitBankPair_spec (cap : ℕ) (flag OP : Fin nr) (dst : Fin (ns + 1))
    (b : Bool) (σ : WState ns nr) (hb : σ.val flag = b.toNat)
    (hd : σ.sh dst = (σ.st dst).length) (hc : σ.val OP + 2 ≤ cap) :
    WExec cap (emitBankPair flag OP dst) σ (appendO σ dst OP [true, b]) 16 := by
  cases b
  · exact WExec.ifrF hb (emitPair_spec cap dst OP false σ hd hc)
  · exact WExec.ifrT (by rw [hb]; decide) (emitPair_spec cap dst OP true σ hd hc)

/-- `lem:print`, paper/paper.tex: the
actual two-bank input consists of its computed dispatch bit and the
same three retained source fields expected by the original-pool machines. -/
theorem poolSourceWord_frame (b : Bool) (source header : List Bool) (width : ℕ) :
    frame (b :: poolSourceWord source header width) = [true, b] ++
      marks (frame (frame source)) ++ marks (frame (frame header)) ++
      marks (frame (natWord width)) ++ marks (List.replicate 8 false) ++ [false] := by
  have hw : poolSourceWord source header width = frame (frame source) ++
      frame (frame header) ++ frame (natWord width) ++ List.replicate 8 false := by
    simp only [poolSourceWord, NearCubicWires.WireExponent3_5.CompilerMachine.Top.loadRec,
      show frame ([] : List Bool) = [false] from rfl,
      List.replicate_succ, List.replicate_zero, List.append_assoc]
    rfl
  change [true, b] ++ frame (poolSourceWord source header width) = _
  rw [hw, Codec.frame_eq_marks]
  simp only [Streaming.marks_append, List.append_assoc]

/-- `lem:print`, paper/paper.tex: the
physical bank input is built from the actual retained indexed call,
actual affine header and original width codec, with eight empty fields. -/
def bankFormatProgram (P : Fin 4 ↪ Fin (ns + 1)) (R : Fin 4 ↪ Fin nr) : WM ns nr :=
  .seq (emitBankPair (R 0) (R 1) (P 3))
    (.seq (appendNestedFieldReset (P 0) (P 3) (R 1) (R 2))
      (.seq (appendNestedFieldReset (P 1) (P 3) (R 1) (R 2))
        (.seq (appendNaturalFieldReset (P 2) (P 3) (R 1) (R 2) (R 3))
          (.seq (emitWordM (P 3) (R 1) (List.replicate 8 false)) (emitC (P 3) (R 1) false)))))

/-- `prop:time`, paper/paper.tex: the
bank input formatter pays all actual finite source bytes and markers;
its target width is copied as a binary codec, never numerically enumerated. -/
def bankFormatClock (source header : List Bool) (width : ℕ) : ℕ :=
  2000 * ((frame source).length + (frame header).length + (natWord width).length + 1)

/-- `lem:print` and `prop:time`, paper/paper.tex: actual retained source data and the
computed bank bit produce exactly one cold tagged pool input, with
all source rewinds, field markers and final delimiters physically paid. -/
theorem bankFormatProgram_spec (cap : ℕ) (P : Fin 4 ↪ Fin (ns + 1))
    (R : Fin 4 ↪ Fin nr) (b : Bool) (source header : List Bool) (width : ℕ)
    (σ : WState ns nr) (hf : σ.val (R 0) = b.toNat)
    (ha : σ.st (P 0) = frame source) (hh : σ.st (P 1) = frame header)
    (hw : σ.st (P 2) = natWord width) (hheads : ∀ i, σ.sh (P i) = 0)
    (hd : σ.st (P 3) = []) (hOP : σ.val (R 1) = 0)
    (hSC : σ.val (R 2) = 0) (hK : σ.val (R 3) = 0)
    (hcap : 4 * ((frame source).length + (frame header).length + (natWord width).length) + 100 ≤ cap) :
    WExec cap (bankFormatProgram P R) σ
      (appendO σ (P 3) (R 1) (frame (b :: poolSourceWord source header width)))
      (bankFormatClock source header width) := by
  have hp {i j : Fin 4} : P i = P j ↔ i = j := P.injective.eq_iff
  have hr {i j : Fin 4} : R i = R j ↔ i = j := R.injective.eq_iff
  have hc := hcap
  simp only [NearCubicWires.RepairOrdinary.frame_length] at hc
  have e0 := emitBankPair_spec cap (R 0) (R 1) (P 3) b σ hf
    (by rw [hheads 3, hd]; rfl) (by rw [hOP]; omega)
  let s0 := appendO σ (P 3) (R 1) [true, b]
  have e1 := appendNestedFieldReset_spec cap (P 0) (P 3) (R 1) (R 2)
    (P.injective.ne (by decide)) (R.injective.ne (by decide)) source [] s0
    (by simp [s0, appendO, hp, ha]) (by simp [s0, appendO, hp, hheads])
    (by simp [s0, appendO, hheads, hd]) (by simp [s0, appendO, hr, hSC])
    (by simp only [s0, appendO_val, Function.update_self, hOP, Nat.zero_add,
        List.length_cons, List.length_nil, NearCubicWires.RepairOrdinary.frame_length]; omega)
  let s1 := appendO s0 (P 3) (R 1) (marks (frame (frame source)))
  have e2 := appendNestedFieldReset_spec cap (P 1) (P 3) (R 1) (R 2)
    (P.injective.ne (by decide)) (R.injective.ne (by decide)) header [] s1
    (by simp [s1, s0, appendO, hp, hh]) (by simp [s1, s0, appendO, hp, hheads])
    (by simp [s1, s0, appendO, hheads, hd]; omega) (by simp [s1, s0, appendO, hr, hSC])
    (by simp only [s1, s0, appendO_val, Function.update_self, hOP, Nat.zero_add,
        List.length_cons, List.length_nil, Codec.marks_length,
        NearCubicWires.RepairOrdinary.frame_length]; omega)
  let s2 := appendO s1 (P 3) (R 1) (marks (frame (frame header)))
  have e3 := appendNaturalFieldReset_spec cap (P 2) (P 3) (R 1) (R 2) (R 3)
    (P.injective.ne (by decide)) (R.injective.ne (by decide))
    (R.injective.ne (by decide)) (R.injective.ne (by decide)) width [] s2
    (by simp [s2, s1, s0, appendO, hp, hw]) (by simp [s2, s1, s0, appendO, hp, hheads])
    (by simp [s2, s1, s0, appendO, hheads, hd, List.length_append, Nat.add_assoc]; omega)
    (by simp [s2, s1, s0, appendO, hr, hSC]) (by simp [s2, s1, s0, appendO, hr, hK])
    (by simp only [s2, s1, s0, appendO_val, Function.update_self, hOP, Nat.zero_add,
        List.length_cons, List.length_nil, Codec.marks_length,
        NearCubicWires.RepairOrdinary.frame_length]; omega)
  let s3 := appendO s2 (P 3) (R 1) (marks (frame (natWord width)))
  have e4 := emitWordM_spec cap (P 3) (R 1) (List.replicate 8 false) s3
    (by simp [s3, s2, s1, s0, appendO, hheads, hd, List.length_append, Nat.add_assoc]; omega)
    (by simp only [s3, s2, s1, s0, appendO_val, Function.update_self, hOP, Nat.zero_add,
        List.length_cons, List.length_nil, List.length_replicate, Codec.marks_length,
        NearCubicWires.RepairOrdinary.frame_length]; omega)
  let s4 := appendO s3 (P 3) (R 1) (marks (List.replicate 8 false))
  have e5 := Codec.emitBit_spec cap (P 3) (R 1) false s4
    (by simp [s4, s3, s2, s1, s0, appendO, hheads, hd, List.length_append, Nat.add_assoc]; omega)
    (by simp only [s4, s3, s2, s1, s0, appendO_val, Function.update_self, hOP, Nat.zero_add,
        List.length_cons, List.length_nil, List.length_replicate, Codec.marks_length,
        NearCubicWires.RepairOrdinary.frame_length]; omega)
  refine (e0.seq (e1.seq (e2.seq (e3.seq (e4.seq e5))))).cast cap ?_ ?_
  · simp only [s4, s3, s2, s1, s0, appendO_append, poolSourceWord_frame, List.append_assoc]
  · unfold bankFormatClock appendNestedFieldCost
    simp only [List.length_replicate, NearCubicWires.RepairOrdinary.frame_length]
    omega

end NearQuarticWires.StageNativeKids
