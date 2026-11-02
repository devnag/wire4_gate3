import Proof.Quartic.StageCertNative.NFirstSource
import Proof.Quartic.StageCert.MomentRuntimeArity
import Proof.Quartic.StagePrintContext.Cost

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells
open StageCert.Tokens

/-- `lem:print` and `prop:time`, paper/paper.tex: the exact retained context length is bounded by its
actual checked source program, not a decoded-field length promise. -/
theorem context_word_length_bound {B1 B2 : ℕ} (r : StageCertTests.PreparedScheduleRequest B1 B2) :
    (StagePrint.Context.word r).length≤100000000*(r.word.length+1)^3 := by
  obtain ⟨z,n,he,hn,hout⟩:=StagePrintContext.contextProgram_run r
  have hh:=he.out_len
  simp only [a0,List.length_nil,zero_add] at hh
  rw [hout,frame_length] at hh
  have hs:=StagePrintContext.contextSteps_bound r
  omega

private theorem cube_succ_bound (M : ℕ) (hM : 1≤M) : (M+1)^3≤8*M^3 := by
  have h1 : 1≤M^3 := Nat.one_le_pow _ _ hM
  have h2 : M≤M^3 := Nat.le_self_pow (by decide) _
  have h3 : M^2≤M^3 := Nat.pow_le_pow_right hM (by decide : 2≤3)
  calc
    (M+1)^3=M^3+3*M^2+3*M+1 := by ring
    _≤8*M^3 := by omega

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual counted original source, including its
once-computed context and low-first index, has fixed polynomial
length in the complete original source runtime scale. -/
theorem TermJob.word_length_scale {B1 B2 : ℕ} (r : TermJob B1 B2) :
    r.word.length≤1000000000*r.moment.runtimeScale^3 := by
  let M:=r.moment.runtimeScale
  have hM : 1000≤M := r.moment.runtimeScale_basic.1
  have hw : r.moment.word.length≤M := r.moment.runtimeScale_basic.2.2
  have hk : r.moment.selected.1.k≤M := by
    have hb:=r.moment.runtimeScale_basic.2.1
    dsimp only [MomentRequest.bodyScale] at hb
    omega
  have hbase : r.base.baseWord.length≤M := by
    have hh:=actualMoment_word r.base r.index
    change r.moment.word=r.base.baseWord++natWord r.index.val at hh
    rw [hh,List.length_append] at hw
    omega
  have hprep : r.base.prepared.word.length≤M :=
    r.moment.prep_length_le.trans r.moment.runtimeScale_basic.2.2
  have hc:=context_word_length_bound r.base.prepared
  have hctx : (StagePrint.Context.word r.base.prepared).length≤800000000*M^3 := by
    calc
      _≤100000000*(r.base.prepared.word.length+1)^3 := hc
      _≤100000000*(M+1)^3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
      _≤100000000*(8*M^3) := Nat.mul_le_mul_left _ (cube_succ_bound M (by omega))
      _=_ := by ring
  have hcount:=count_bits r.base
  have hindex : natBitLength r.index.val≤natBitLength (termCount r.base) := by
    exact Nat.add_le_add_right (Nat.log_mono_right r.index.isLt.le) 1
  have hcountM : natBitLength (termCount r.base)≤4*M+1 := by
    change r.moment.selected.1.k≤M at hk
    have he : r.base.prepared.selected.1.k=r.moment.selected.1.k := rfl
    rw [he] at hcount
    omega
  have hpow : M≤M^3 := Nat.le_self_pow (by decide) _
  have hone : 1≤M^3 := Nat.one_le_pow _ _ (by omega)
  dsimp only [M] at hctx hpow hone
  unfold TermJob.word cachedSourceWord
  simp only [List.length_append,natWord_length]
  omega

/-- `lem:print`, paper/paper.tex: adding the
computed original-n header does not introduce any new exponential
source census or require index-based word-width allocation. -/
theorem nFirstWord_length_scale {B1 B2 : ℕ} (r : TermJob B1 B2) :
    (nFirstWord r).length≤10000000000*r.moment.runtimeScale^3 := by
  have hword:=r.word_length_scale
  have hn : r.moment.call.n≤r.moment.runtimeScale := by
    dsimp only [MomentRequest.runtimeScale]
    omega
  have hbits:=NearCubicGates.Close.Dispatch.natBitLength_le_succ r.moment.call.n
  have hpow : r.moment.runtimeScale≤r.moment.runtimeScale^3 := Nat.le_self_pow (by decide) _
  have hone : 1≤r.moment.runtimeScale^3 :=
    Nat.one_le_pow _ _ (by have h:=r.moment.runtimeScale_basic.1;omega)
  unfold nFirstWord
  simp only [List.length_append,natWord_length]
  omega

noncomputable def sharedSourceCoefficient (B1 B2 : ℕ) : ℕ :=
  10000000000*(momentRuntimeCoefficient B1 B2)^3

noncomputable def sharedSourceExponent (B1 B2 : ℕ) : ℕ :=
  3*momentRuntimeExponent B1 B2

/-- `prop:time`, paper/paper.tex: the literal
actual internal source has an original-arity polynomial bound,
uniform in the whole test, low-first index and proposed witness. -/
theorem nFirstWord_length_arity {B1 B2 : ℕ} (r : TermJob B1 B2) :
    (nFirstWord r).length ≤ sharedSourceCoefficient B1 B2*
      (r.moment.call.n+1)^sharedSourceExponent B1 B2 := by
  calc
    _≤10000000000*r.moment.runtimeScale^3 := nFirstWord_length_scale r
    _≤10000000000*(momentRuntimeCoefficient B1 B2*
        (r.moment.call.n+1)^momentRuntimeExponent B1 B2)^3 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left r.moment.runtimeScale_arity _)
    _=_ := by
      unfold sharedSourceCoefficient sharedSourceExponent
      rw [mul_pow,←pow_mul,Nat.mul_comm (momentRuntimeExponent B1 B2) 3]
      ring

end NearQuarticWires.StageCertNative
