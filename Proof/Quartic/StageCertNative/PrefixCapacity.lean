import Proof.Quartic.StageCertNative.SourceLengths
import Proof.Quartic.StageCertNative.PrefixMetadata
import Proof.Quartic.StageEntryAllocation.Width

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open StageCert.Tokens

/-- `lem:print`, paper/paper.tex: the selected
literal moment degree fits original arity before any column is tested. -/
theorem TermJob.degree_le_arity {B1 B2 : ℕ} (r : TermJob B1 B2) :
    r.moment.packet.degree≤r.moment.call.n := by
  have hs:=r.moment.rules
  have hh:=hs.moment_degree
  rw [hs.m_eq] at hh
  have hd : r.moment.selected.1.Dmax≤r.moment.call.n := by
    rw [hs.Dmax_eq]
    exact Nat.findGreatest_le
      (P:=Cells.ParameterArithmetic.DegreePass (Builder.callInput r.moment.call).n
        r.moment.selected.1.m r.moment.selected.1.k r.moment.selected.1.Uocc)
      (n:=(Builder.callInput r.moment.call).n)
  exact hh.trans hd

/-- `lem:print`, paper/paper.tex: the binary
ordinal height is controlled by the actual eight-coordinate walk census. -/
theorem TermJob.index_bits {B1 B2 : ℕ} (r : TermJob B1 B2) :
    natBitLength r.index.val≤4*r.moment.call.n+1 := by
  have hc:=count_bits r.base
  have hi : natBitLength r.index.val≤natBitLength (termCount r.base) :=
    Nat.add_le_add_right (Nat.log_mono_right r.index.isLt.le) 1
  have hd:=r.degree_le_arity
  change 16*r.moment.selected.1.Xmax+8*r.moment.selected.1.k≤r.moment.call.n at hd
  change natBitLength (termCount r.base)≤4*r.moment.selected.1.k+1 at hc
  omega

noncomputable def prefixCapacity {B1 B2 : ℕ} (r : TermJob B1 B2) : ℕ :=
  (nFirstWord r).length+Cells.nativeCertificateBits B1 r.moment.call.n+
    nativeBitsFactor B1+nativeBitsExponentValue B1+r.moment.call.n+
    r.moment.packet.degree+prefixScalarBits r+200

noncomputable def prefixCapacityCoefficient (B1 B2 : ℕ) : ℕ :=
  sharedSourceCoefficient B1 B2+3*nativeBitsFactor B1+nativeBitsExponentValue B1+1000

noncomputable def prefixCapacityExponent (B1 B2 : ℕ) : ℕ :=
  sharedSourceExponent B1 B2+nativeBitsExponentValue B1+2

/-- `prop:time`, paper/paper.tex: one fixed
original-arity polynomial bounds the real input, scalar encodings and
all exact coefficient-width arithmetic, on every proposed witness. -/
theorem prefixCapacity_arity {B1 B2 : ℕ} (r : TermJob B1 B2) :
    prefixCapacity r≤prefixCapacityCoefficient B1 B2*
      (r.moment.call.n+1)^prefixCapacityExponent B1 B2 := by
  let n:=r.moment.call.n
  let F:=nativeBitsFactor B1
  let E:=nativeBitsExponentValue B1
  let C:=sharedSourceCoefficient B1 B2
  let Z:=(n+1)^prefixCapacityExponent B1 B2
  have hp : 1≤Z := Nat.one_le_pow _ _ (by omega)
  have hn : n≤Z := (Nat.le_succ _).trans
    (Nat.le_self_pow (by dsimp only [prefixCapacityExponent];omega) _)
  have hs : (nFirstWord r).length≤C*Z :=
    (nFirstWord_length_arity r).trans (Nat.mul_le_mul_left _
      (Nat.pow_le_pow_right (by omega) (by dsimp only [prefixCapacityExponent];omega)))
  have hb : Cells.nativeCertificateBits B1 n≤(F+2)*Z := by
    have hh : (n+1)^E≤Z := Nat.pow_le_pow_right (by omega)
      (by dsimp only [E,prefixCapacityExponent];omega)
    have hmul:=Nat.mul_le_mul_left F hh
    change F*(n+1)^E+2≤(F+2)*Z
    nlinarith only [hmul,hp]
  have hdegree : r.moment.packet.degree≤n := r.degree_le_arity
  have hi : natBitLength r.index.val≤4*n+1 := r.index_bits
  have hnb:=NearCubicGates.Close.Dispatch.natBitLength_le_succ n
  have hdb:=NearCubicGates.Close.Dispatch.natBitLength_le_succ r.moment.packet.degree
  have hbb:=NearCubicGates.Close.Dispatch.natBitLength_le_succ
    (Cells.nativeCertificateBits B1 n)
  have hscalar : prefixScalarBits r≤6*n+Cells.nativeCertificateBits B1 n+4 := by
    change natBitLength n+natBitLength r.index.val+
      natBitLength r.moment.packet.degree+natBitLength (Cells.nativeCertificateBits B1 n)≤_
    omega
  have hconstant : F+E+204≤(F+E+204)*Z := Nat.le_mul_of_pos_right _ hp
  change (nFirstWord r).length+Cells.nativeCertificateBits B1 n+F+E+n+
    r.moment.packet.degree+prefixScalarBits r+200≤(C+3*F+E+1000)*Z
  nlinarith only [hs,hb,hdegree,hscalar,hn,hconstant,hp]

noncomputable def prefixSizes (B1 B2 : ℕ) : Sz :=
  StageEntryAllocation.sizes (prefixCapacityCoefficient B1 B2) (prefixCapacityExponent B1 B2)

/-- `lem:print` and `prop:time`, paper/paper.tex: allocation is selected by the computed original-n
header and covers the whole real prefix execution without a capacity input. -/
theorem prefixSizes_required {B1 B2 : ℕ} (r : TermJob B1 B2) :
    prefixCapacity r+10≤(prefixSizes B1 B2).W (leadOnes (nFirstWord r)) := by
  have hheader : leadOnes (nFirstWord r)=natBitLength r.moment.call.n := by
    unfold nFirstWord
    exact NearCubicGates.Close.CounterMachine.PrefixProg.leadOnes_natWord _ _
  have hn : r.moment.call.n+1≤2^natBitLength r.moment.call.n := lt_natBitLength _
  let C:=prefixCapacityCoefficient B1 B2
  let E:=prefixCapacityExponent B1 B2
  have hp : (r.moment.call.n+1)^E≤2^((E+2)*natBitLength r.moment.call.n) := by
    calc
      _≤(2^natBitLength r.moment.call.n)^E := Nat.pow_le_pow_left hn _
      _=2^(E*natBitLength r.moment.call.n) := by rw [←pow_mul,Nat.mul_comm]
      _≤_ := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by omega))
  have hfit:=Nat.mul_le_mul_right (10*(C+1)) hp
  have hone : 1≤(r.moment.call.n+1)^E := Nat.one_le_pow _ _ (by omega)
  have hm:=prefixCapacity_arity r
  rw [hheader]
  change prefixCapacity r+10≤2^((E+2)*natBitLength r.moment.call.n)*(10*(C+1))
  change prefixCapacity r≤C*(r.moment.call.n+1)^E at hm
  nlinarith only [hfit,hone,hm]

end NearQuarticWires.StageCertNative
