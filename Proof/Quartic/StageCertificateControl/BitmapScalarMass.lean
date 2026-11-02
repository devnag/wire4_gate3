import Proof.Quartic.StageCertificateControl.BitmapRequest

/-!
# Polynomial scalar work surrounding the full native bitmap

Paper: `prop:time`, paper/paper.tex.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open NearCubicGates.Close.CellsPack (Gof)
open StageCertTests (PreparedPolynomial PreparedScheduleRequest)

/-- `prop:time`, paper/paper.tex: all scalar
bitmap work uses the original preparation, public test count, fixed
native-width polynomial and actual empty-callee compilation scale.
The exponential native column census is excluded from this quantity. -/
noncomputable def bitmapScalarMass {B1 B2 : ℕ} (coefficient degree : ℕ)
    (r : PreparedScheduleRequest B1 B2) : ℕ :=
  StageCertTests.prepScheduleMass r.call r.selected.1+r.word.length+
    (StageCertTests.certificateMetadata r.selected.1 r.call.kind).length+
    coefficient*(r.call.n+1)^degree+
    Gof StageRecovery.packetCallee (bitmapSizes B1 B2 coefficient degree) (leadOnes r.word)+10

/-- `prop:time`, paper/paper.tex: the actual
bitmap arithmetic workspace has polynomial numeric size in the original
call word, even when the later native stream is exponentially long. -/
theorem bitmapWorkspacePolynomial (B1 B2 coefficient degree : ℕ) :
    PreparedPolynomial (B1 := B1) (B2 := B2) (fun r =>
      (bitmapSizes B1 B2 coefficient degree).W (leadOnes r.word)) := by
  let z := bitmapSizes B1 B2 coefficient degree
  let D := z.c1
  refine ⟨z.a1*4^D,D,fun r => ?_⟩
  have hhead : leadOnes r.word=1+natBitLength r.call.n := by
    rw [r.word_eq]
    simpa only [List.append_assoc] using StageMain.taggedCall_header_width r.call
      (Program.parametersWord r.selected.1++frame (Program.witnessPrefix r.call r.selected.1 r.witness))
  have hbits := NearCubicGates.Close.CounterMachine.PrefixProg.pow_nbl_le r.call.n
  have hbase : 2*2^natBitLength r.call.n≤4*(r.call.n+1) := by omega
  have halg (d b a : ℕ) : 2^(d*(1+b))*a=(2*2^b)^d*a := by
    rw [Nat.mul_comm d (1+b),Nat.pow_mul,Nat.pow_add,pow_one]
  have hwidth : z.W (leadOnes r.word)≤z.a1*4^D*(r.call.n+1)^D := by
    change 2^(D*leadOnes r.word)*z.a1≤_
    rw [hhead,halg]
    calc
      (2*2^natBitLength r.call.n)^D*z.a1≤(4*(r.call.n+1))^D*z.a1 :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hbase D)
      _ = _ := by rw [mul_pow];ring
  exact hwidth.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
    (Nat.add_le_add_right (Cells.dispatched_n_le_callWord r.dispatched) 1) D))

/-- `prop:time`, paper/paper.tex: the literal
scalar compilation factor for the bitmap program is a polynomial
original-source quantity and includes every fixed allocator parameter. -/
theorem bitmapCompilationPolynomial (B1 B2 coefficient degree : ℕ) :
    PreparedPolynomial (B1 := B1) (B2 := B2) (fun r =>
      Gof StageRecovery.packetCallee (bitmapSizes B1 B2 coefficient degree) (leadOnes r.word)) :=
  PreparedPolynomial.compilationScale_of (bitmapSizes B1 B2 coefficient degree) StageRecovery.packetCallee
    (bitmapWorkspacePolynomial B1 B2 coefficient degree) PreparedPolynomial.header
    (by intro n;simp [bitmapSizes,Sz.Lk]) (by intro n;simp [bitmapSizes,Sz.Bk])

/-- `prop:time`, paper/paper.tex: every
component of the scalar bitmap mass has a proved polynomial bound
in the literal original call word, uniformly over witnesses. -/
theorem bitmapScalarMassPolynomial (B1 B2 coefficient degree : ℕ) :
    PreparedPolynomial (B1 := B1) (B2 := B2) (bitmapScalarMass coefficient degree) := by
  have hm : PreparedPolynomial (B1 := B1) (B2 := B2)
      (fun r => StageCertTests.prepScheduleMass r.call r.selected.1) :=
    (((((((PreparedPolynomial.callLength.add (PreparedPolynomial.const 1)).add
      (PreparedPolynomial.hint.add (PreparedPolynomial.const 1))).add
      ((PreparedPolynomial.scalar .k).add (PreparedPolynomial.const 1))).add
      ((PreparedPolynomial.scalar .chainLength).add (PreparedPolynomial.const 1))).add
      PreparedPolynomial.parameterReader).add PreparedPolynomial.arityBits).add
      PreparedPolynomial.kindBits).add (PreparedPolynomial.const 1)
  have hT : PreparedPolynomial (B1 := B1) (B2 := B2) (fun r =>
      (StageCertTests.certificateMetadata r.selected.1 r.call.kind).length) := by
    obtain ⟨K,e,hK⟩ := countHeaderValuePolyCost B1 B2
    refine ⟨K,e,fun r => ?_⟩
    have h := hK r.call r.witness
    simpa only [countHeaderValue,r.dispatched] using h
  have hW : PreparedPolynomial (B1 := B1) (B2 := B2)
      (fun r => coefficient*(r.call.n+1)^degree) := by
    have h : PreparedPolynomial (B1 := B1) (B2 := B2)
        (fun r => coefficient*((callWord r.call).length+1)^degree) :=
      (PreparedPolynomial.const coefficient).mul
      ((PreparedPolynomial.callLength.add (PreparedPolynomial.const 1)).pow degree)
    refine h.mono ?_
    intro r
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
      (Nat.add_le_add_right (Cells.dispatched_n_le_callWord r.dispatched) 1) degree)
  exact ((((hm.add PreparedPolynomial.inputLength).add hT).add hW).add
    (bitmapCompilationPolynomial B1 B2 coefficient degree)).add (PreparedPolynomial.const 10)

end NearQuarticWires.StageCertificateControl
