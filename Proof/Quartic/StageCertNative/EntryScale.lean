import Proof.Quartic.StageCertNative.EntryMagnitude
import Proof.Quartic.StageCertNative.PrefixCapacity
import Proof.Quartic.StageCertNative.EntryRequest

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells
open StageCert.Tokens

noncomputable def entryScale {B1 B2 : ℕ} (r : TermJob B1 B2) : ℕ :=
  r.moment.runtimeScale+Cells.nativeCertificateBits B1 r.moment.call.n+1

/-- `lem:print`, paper/paper.tex: the actual
source scale and polynomial coefficient-bit field bound every
original exact formatter input, including all proposed witnesses. -/
theorem exactEntry_magnitude_scale {B1 B2 : ℕ} (r : TermJob B1 B2) :
    (exactEntry r.moment).sizingMagnitude≤10^28*(entryScale r)^8 := by
  let S:=entryScale r
  let e:=exactEntry r.moment
  have hM:=r.moment.runtimeScale_basic
  have hn0 : r.moment.call.n≤r.moment.runtimeScale := by
    dsimp only [MomentRequest.runtimeScale]
    omega
  have hS : 1≤S := by dsimp only [S,entryScale];omega
  have hn : e.header.call.n+1≤S := by
    change r.moment.call.n+1≤r.moment.runtimeScale+Cells.nativeCertificateBits B1 r.moment.call.n+1
    omega
  have hn' : r.moment.call.n+1≤S := hn
  have hg : (Builder.allGates e.header.call).length≤S := by
    have hh:=hM.2.1
    dsimp only [MomentRequest.bodyScale] at hh
    change (Builder.allGates r.moment.call).length≤
      r.moment.runtimeScale+Cells.nativeCertificateBits B1 r.moment.call.n+1
    omega
  have hd : e.degree≤S := r.degree_le_arity.trans (by change r.moment.call.n≤S;omega)
  have hc0 : e.coefficientBits≤S := by
    change Cells.nativeCertificateBits B1 r.moment.call.n≤
      r.moment.runtimeScale+Cells.nativeCertificateBits B1 r.moment.call.n+1
    omega
  have hSq : S≤S^2 := Nat.le_self_pow (by decide) _
  have hc : e.coefficientBits≤S^2 := hc0.trans hSq
  have hscale : natBitLength e.scale≤S^2 := by
    have hh:=NearCubicGates.Close.Dispatch.natBitLength_le_succ
      (Cells.nativeCertificateBits B1 r.moment.call.n)
    have ht : Cells.nativeCertificateBits B1 r.moment.call.n+1≤S := by
      dsimp only [S,entryScale]
      omega
    exact (hh.trans ht).trans hSq
  have hi : natBitLength e.walkCode.val≤4*S+1 :=
    r.index_bits.trans (by change 4*r.moment.call.n+1≤4*S+1;omega)
  have hp : r.base.prepared.word.length+1≤S := by
    have hh:=r.moment.prep_length_le.trans hM.2.2
    change r.base.prepared.word.length≤r.moment.runtimeScale at hh
    dsimp only [S,entryScale]
    omega
  have hcontext : e.contextWord.length≤10^25*S^8+1 := by
    have hc:=context_word_length_bound r.base.prepared
    have he:=actualEntry_context r.base r.index
    change e.contextWord=StagePrint.Context.word r.base.prepared at he
    rw [he]
    have h3 : S^3≤S^8 := Nat.pow_le_pow_right hS (by decide)
    have hh : (StagePrint.Context.word r.base.prepared).length≤100000000*S^8 :=
      hc.trans ((Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hp _)).trans
        (Nat.mul_le_mul_left _ h3))
    omega
  exact entryMagnitude_bound e S hS hn hg hd hc hscale hi hcontext

noncomputable def entryScaleCoefficient (B1 B2 : ℕ) : ℕ :=
  momentRuntimeCoefficient B1 B2+nativeBitsFactor B1+3

noncomputable def entryScaleExponent (B1 B2 : ℕ) : ℕ :=
  momentRuntimeExponent B1 B2+nativeBitsExponentValue B1+1

/-- `prop:time`, paper/paper.tex: exact source
and coefficient widths have one original-arity polynomial uniform
over the test and every low-first whole-test term ordinal. -/
theorem entryScale_arity {B1 B2 : ℕ} (r : TermJob B1 B2) :
    entryScale r≤entryScaleCoefficient B1 B2*
      (r.moment.call.n+1)^entryScaleExponent B1 B2 := by
  let n:=r.moment.call.n
  let Z:=(n+1)^entryScaleExponent B1 B2
  have hp : 1≤Z := Nat.one_le_pow _ _ (by omega)
  have hM : r.moment.runtimeScale ≤ momentRuntimeCoefficient B1 B2*Z :=
    r.moment.runtimeScale_arity.trans (Nat.mul_le_mul_left _
      (Nat.pow_le_pow_right (by omega) (by dsimp only [entryScaleExponent];omega)))
  have hF : nativeBitsFactor B1*(n+1)^nativeBitsExponentValue B1≤nativeBitsFactor B1*Z :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega)
      (by dsimp only [entryScaleExponent];omega))
  change r.moment.runtimeScale+(nativeBitsFactor B1*(n+1)^nativeBitsExponentValue B1+2)+1≤
    (momentRuntimeCoefficient B1 B2+nativeBitsFactor B1+3)*Z
  nlinarith only [hM,hF,hp]

noncomputable def entrySizingCoefficient (B1 B2 : ℕ) : ℕ :=
  10^28*(entryScaleCoefficient B1 B2)^8

noncomputable def entrySizingExponent (B1 B2 : ℕ) : ℕ :=
  8*entryScaleExponent B1 B2

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual exact request belongs to the fixed
bounded domain of the ordinary native formatter, without extra bytes. -/
theorem exactEntry_sizing {B1 B2 : ℕ} (r : TermJob B1 B2) :
    (exactEntry r.moment).sizingMagnitude≤entrySizingCoefficient B1 B2*
      (r.moment.call.n+1)^entrySizingExponent B1 B2 := by
  calc
    _≤10^28*(entryScale r)^8 := exactEntry_magnitude_scale r
    _≤10^28*(entryScaleCoefficient B1 B2*
      (r.moment.call.n+1)^entryScaleExponent B1 B2)^8 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (entryScale_arity r) _)
    _=_ := by
      unfold entrySizingCoefficient entrySizingExponent
      rw [mul_pow,←pow_mul,Nat.mul_comm (entryScaleExponent B1 B2) 8]
      ring

end NearQuarticWires.StageCertNative
