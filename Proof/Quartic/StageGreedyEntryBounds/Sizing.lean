import Proof.Quartic.StageGreedyEntryBounds.Lengths
import Proof.Quartic.StageNativeWidth.Polynomial

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyEntryBounds

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open NearCubicGates.Close.Interfaces.Formats
open StagePrint

/-- `lem:print`, paper/paper.tex: the actual
allocator magnitude depends polynomially on the original small source
bounds while retaining only logarithmic dependence on the Terms bytes. -/
theorem sizingMagnitude_bound (r : EntryFormat.Request true) (S : ℕ)
    (hS : 1≤S) (hn : r.header.call.n+1≤S)
    (hg : (Builder.allGates r.header.call).length≤S) (hd : r.degree≤S)
    (hc : r.coefficientBits≤S^2) (hi : natBitLength r.walkCode.val≤4*S+1)
    (hcontext : r.contextWord.length≤10^25*S^8+1) :
    r.sizingMagnitude≤10^28*S^8 := by
  let n:=r.header.call.n
  let L:=r.toRowContext.nativeFieldWidth
  let V:=17*(Builder.allGates r.header.call).length
  have hL : L≤16*S^2 :=
    (StageNativeWidth.nativeFieldWidth_le r.toRowContext).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn _))
  have hV : V≤17*S := Nat.mul_le_mul_left _ hg
  have hSq : S≤S^2 := Nat.le_self_pow (by decide) _
  have hn0 : n≤S := by dsimp [n];omega
  have hn2 : (n+1)^2≤S^2 := Nat.pow_le_pow_left hn _
  have hscale : natBitLength r.scale≤S^2 := hc
  have hnb : natBitLength n≤S :=
    (NearCubicGates.Close.Dispatch.natBitLength_le_succ _).trans hn
  have hdb : natBitLength r.degree≤S+1 :=
    (NearCubicGates.Close.Dispatch.natBitLength_le_succ _).trans (Nat.add_le_add_right hd 1)
  have ht:=termsWord_bitLength V r.coefficientBits r.terms r.terms_nodup r.coefficient_bits
  have hV2:=Nat.pow_le_pow_left hV 2
  have hterms : natBitLength (termsWord r.terms).length≤1000*S^2 := by
    unfold recordHeight at ht
    nlinarith only [ht,hV,hV2,hc,hS,hSq]
  let prefixBytes:=natWord n++r.contextWord++natWord r.walkCode.val++natWord r.degree++natWord r.scale
  have hp : prefixBytes.length≤r.contextWord.length+2*S^2+12*S+8 := by
    have hc0:=NearCubicGates.Close.CounterAsm.natWord_len n
    have hc1:=NearCubicGates.Close.CounterAsm.natWord_len r.walkCode.val
    have hc2:=NearCubicGates.Close.CounterAsm.natWord_len r.degree
    have hc3:=NearCubicGates.Close.CounterAsm.natWord_len r.scale
    simp only [prefixBytes,List.length_append,hc0,hc1,hc2,hc3]
    omega
  have hword : natBitLength r.word.length≤prefixBytes.length+
      natBitLength (termsWord r.terms).length+5 := by
    have heq : r.word=prefixBytes++frame (termsWord r.terms) := by
      simp only [EntryFormat.Request.word,prefixBytes,n,List.append_assoc]
    rw [heq,List.length_append]
    have ha:=bitLength_add_prefix prefixBytes.length (frame (termsWord r.terms)).length
    have hb:=bitLength_frame_length (termsWord r.terms)
    omega
  have hdiv : (n+1)/2≤S := (Nat.div_le_self _ _).trans hn
  have hfirst : r.degree+2≤3*S := by omega
  have hsecond : L+2*((n+1)/2)+r.degree+4≤23*S^2 := by nlinarith only [hL,hdiv,hd,hS,hSq]
  have hprod : (r.degree+2)*(L+2*((n+1)/2)+r.degree+4)≤69*S^3 := by
    calc
      _≤(3*S)*(23*S^2) := Nat.mul_le_mul hfirst hsecond
      _=_ := by ring
  have hhead : 4*(n+1)^2+n+20≤30*S^2 := by nlinarith only [hn2,hn0,hS,hSq]
  have hrest : r.coefficientBits+n+L+r.degree+30≤50*S^2 := by nlinarith only [hc,hn0,hL,hd,hS,hSq]
  have h1 : 1≤S^8 := Nat.one_le_pow _ _ hS
  have h2 : S^2≤S^8 := Nat.pow_le_pow_right hS (by decide)
  have h3 : S^3≤S^8 := Nat.pow_le_pow_right hS (by decide)
  have h8 : S≤S^8 := Nat.le_self_pow (by decide) _
  change 4*(n+1)^2+n+20+
    ((r.degree+2)*(L+2*((n+1)/2)+r.degree+4)+r.coefficientBits+n+L+r.degree+30)+
    natBitLength r.word.length+natBitLength r.scale+natBitLength r.walkCode.val+
    natBitLength r.degree+100≤10^28*S^8
  omega

end NearQuarticWires.StageGreedyEntryBounds
