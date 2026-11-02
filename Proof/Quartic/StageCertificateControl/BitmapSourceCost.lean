import Proof.Quartic.StageCertificateControl.BitmapBounds
import Proof.Quartic.StageCertificateControl.FoldCost

/-!
# One native census times scalar work in the bitmap program

Paper: `prop:time`, paper/paper.tex.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Interfaces

/-- `prop:time`, paper/paper.tex: reading
the original call, parameters and retained witness has polynomial
scalar work before the native stream is traversed. -/
theorem preparedInputCost_scalar_bound {B1 B2 coefficient degree : ℕ}
    (r : BitmapRequest B1 B2 coefficient degree) (p : Program.Selected r.call)
    (M : ℕ) (h : BitmapScalarBounds r p M) :
    preparedInputCost r.call p.1 (StageCertTests.scheduleHint p.1)
      (Program.witnessPrefix r.call p.1 r.witness)≤10000*M^3 := by
  have hc := Nat.pow_le_pow_left h.call 3
  have hb : natBitLength r.call.n≤M := (Control.natBitLength_le_self_succ r.call.n).trans h.arity
  have hm2 : 1≤M^2 := Nat.one_le_pow _ _ (by have := h.positive;omega)
  have hm3 : M≤M^3 := by
    have hh := Nat.mul_le_mul_left M hm2
    simpa only [mul_one,pow_succ,Nat.mul_comm] using hh
  unfold preparedInputCost
  nlinarith only [h.call,h.reader,h.witness,h.positive,hb,hc,hm3]

/-- `prop:time`, paper/paper.tex: the full
test-major conjunction has linear native-census work, with polynomial
dependence on its actual scalar count and signed record width. -/
theorem bitmapFoldCost_scalar_bound {B1 B2 coefficient degree : ℕ}
    (r : BitmapRequest B1 B2 coefficient degree) (p : Program.Selected r.call)
    (hd : Program.dispatch B1 B2 r.call=some p) (M : ℕ) (h : BitmapScalarBounds r p M) :
    testFoldCost r.tests≤211*(paddedCount r.call.n p.1.k+1)*M^3 := by
  let N := paddedCount r.call.n p.1.k
  have hf := testFoldCost_le r.tests N M (r.lengths p hd)
    (fun t ht => (Nat.le_succ t.width).trans (h.width t ht)) h.threshold
    (fun t ht => (Control.natBitLength_le_self_succ t.width).trans (h.width t ht))
  have hT := Nat.pow_le_pow_left h.count 2
  have hi : 100*(N+1)*(M+1)+11≤211*(N+1)*M := by
    have hm := h.positive
    nlinarith
  have hh := Nat.mul_le_mul hT hi
  calc
    testFoldCost r.tests≤(r.tests.length+1)^2*(100*(N+1)*(M+1)+11) := hf
    _ ≤ M^2*(211*(N+1)*M) := hh
    _ = _ := by ring

/-- `prop:time`, paper/paper.tex: all cold
bitmap instructions, framing included, cost one native census times
a fixed polynomial in the original-source scalar mass. -/
theorem bitmapSourceSteps_scalar_bound {B1 B2 coefficient degree : ℕ}
    (r : BitmapRequest B1 B2 coefficient degree) (p : Program.Selected r.call)
    (hd : Program.dispatch B1 B2 r.call=some p) (M : ℕ) (h : BitmapScalarBounds r p M) :
    r.sourceSteps≤100000*(paddedCount r.call.n p.1.k+1)*M^3 := by
  let N := paddedCount r.call.n p.1.k
  have hi := preparedInputCost_scalar_bound r p M h
  have hf := bitmapFoldCost_scalar_bound r p hd M h
  have hb : natBitLength r.tests.length≤M :=
    (Control.natBitLength_le_self_succ r.tests.length).trans h.count
  have hm2 : 1≤M^2 := Nat.one_le_pow _ _ (by have := h.positive;omega)
  have hm3 : M≤M^3 := by
    have hh := Nat.mul_le_mul_left M hm2
    simpa only [mul_one,pow_succ,Nat.mul_comm] using hh
  have hpos : 1≤M^3 := Nat.one_le_pow _ _ (by have := h.positive;omega)
  have hM := Nat.le_mul_of_pos_left (M^3) (Nat.succ_pos N)
  have hN := Nat.mul_le_mul_left (N+1) hpos
  rw [BitmapRequest.sourceSteps,hd]
  unfold preparedFoldCost
  change testFoldCost r.tests≤211*(N+1)*M^3 at hf
  change 3*(preparedInputCost r.call p.1 (StageCertTests.scheduleHint p.1)
      (Program.witnessPrefix r.call p.1 r.witness)+
    (150+(100*(r.call.n+1)+((30*natBitLength r.tests.length+32)+
      (testFoldCost r.tests+21*N+24)+1)+1)+1)+1)+13≤100000*(N+1)*M^3
  nlinarith only [hi,hf,hb,h.arity,h.positive,hm3,hM,hN]

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual signed bitmap input has
linear native-census length, including preparation and every header. -/
theorem bitmapInputLength_scalar_bound {B1 B2 coefficient degree : ℕ}
    (r : BitmapRequest B1 B2 coefficient degree) (p : Program.Selected r.call)
    (hd : Program.dispatch B1 B2 r.call=some p) (M : ℕ) (h : BitmapScalarBounds r p M) :
    r.word.length≤100*(paddedCount r.call.n p.1.k+1)*M^3 := by
  let N := paddedCount r.call.n p.1.k
  have hs := nativeTestStream_length_le r.tests N M (r.lengths p hd)
    (fun t ht => (Nat.le_succ t.width).trans (h.width t ht)) h.threshold
    (fun t ht => (Control.natBitLength_le_self_succ t.width).trans (h.width t ht))
  have hT : r.tests.length≤M := by have := h.count;omega
  have hM : M+1≤2*M := by have := h.positive;omega
  have hn := Nat.mul_le_mul hT (Nat.mul_le_mul_left (10*(N+1)) hM)
  have hn' : (nativeTestStream r.tests).length≤20*(N+1)*M^2 := by nlinarith only [hs,hn]
  have hp := Nat.pow_le_pow_right (by have := h.positive;omega : 1≤M) (by decide : 2≤3)
  have hp' := Nat.mul_le_mul_left (20*(N+1)) hp
  have hm2 : 1≤M^2 := Nat.one_le_pow _ _ (by have := h.positive;omega)
  have hm3 : M≤M^3 := by
    have hh := Nat.mul_le_mul_left M hm2
    simpa only [mul_one,pow_succ,Nat.mul_comm] using hh
  have hn3 := Nat.le_mul_of_pos_left (M^3) (Nat.succ_pos N)
  have hb : natBitLength r.tests.length≤M :=
    (Control.natBitLength_le_self_succ r.tests.length).trans h.count
  unfold BitmapRequest.word
  rw [List.length_append,List.length_append,NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_length]
  nlinarith only [hn',hp',hm3,hn3,hb,h.preparation,h.positive]

end NearQuarticWires.StageCertificateControl
