import Proof.Quartic.StageCertNative.Cuts
import Proof.Quartic.StagePrint.NativeRequests
import Proof.Quartic.StageNativeWidth.NativeCuts

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.SourceInterfaces
open NearCubicWires.WireExponent3_5
open StageCertificateControl StageCert.Tokens

/-- `lem:print`, paper/paper.tex: the actual
whole-test equality census, including all N⁸ walks, satisfies the
native rectangular gate-square guard under the unchanged100 reserve. -/
theorem wholeCuts_square {B1 B2 : ℕ} (r : IndexedRequest B1 B2) :
    (2*(wholeCuts r).length)*(2*(wholeCuts r).length)≤
      rectangularInnerDimension (2^PrimT.C4Geo.dRow (zeroMoment r).rules.starParams) := by
  let hs:=(zeroMoment r).rules
  let free:=r.prepared.call.n-r.prepared.selected.1.k
  let q:=free/100
  have hfree : 200≤free := by
    have h:=hs.initial_degree
    change 100*(r.prepared.selected.1.m*r.prepared.selected.1.k+2+
      0*Nat.clog 2 r.prepared.selected.1.Uocc)≤free at h
    omega
  have hq : 2≤q := (Nat.le_div_iff_mul_le (by decide)).mpr hfree
  have hqmul : 100*q≤free := by
    simpa only [Nat.mul_comm] using Nat.div_mul_le_self free 100
  have hsum:=Builder.centerCount_eq r.prepared.call hs
  have hbalance:=hs.starParams.centerBits_balanced.1
  have hdim : free≤2*PrimT.C4Geo.dRow hs.starParams := by
    change hs.starParams.rightCenterBits≤hs.starParams.leftCenterBits at hbalance
    change free=hs.starParams.leftCenterBits+hs.starParams.rightCenterBits at hsum
    change free≤2*hs.starParams.leftCenterBits
    omega
  have he : 20*(q+1)≤PrimT.C4Geo.dRow hs.starParams := by
    have hh : 40*q+40≤100*q := by omega
    omega
  have hcount : 2*(wholeCuts r).length≤2^(q+1) := by
    have h:=Nat.mul_le_mul_left 2 (wholeCuts_count r)
    change 2*(wholeCuts r).length≤2*2^q at h
    simpa only [pow_succ,Nat.mul_comm] using h
  have hp : (2*(wholeCuts r).length)^20≤2^PrimT.C4Geo.dRow hs.starParams := by
    calc
      _≤(2^(q+1))^20 := Nat.pow_le_pow_left hcount _
      _=2^(20*(q+1)) := by rw [←pow_mul,Nat.mul_comm]
      _≤_ := Nat.pow_le_pow_right (by decide) he
  have hh : ((2*(wholeCuts r).length)*(2*(wholeCuts r).length))^10≤
      (rectangularInnerDimension (2^PrimT.C4Geo.dRow hs.starParams))^10 := by
    calc
      _=(2*(wholeCuts r).length)^20 := by ring
      _≤2^PrimT.C4Geo.dRow hs.starParams := hp
      _≤_ := le_integerCeilRoot_pow (by decide : 0<10)
  exact (Nat.pow_le_pow_iff_left (by decide : 10≠0)).mp hh

/-- `lem:print`, paper/paper.tex: a single
actual common-generator request contains every original signed equality
stream, at one uniform polynomial coefficient field width. -/
noncomputable def wholeRequest {B1 B2 : ℕ} (r : IndexedRequest B1 B2) :
    StagePrint.NativeStreamRequest where
  parameters:=(zeroMoment r).rules.starParams
  fieldWidth:=commonWidth r
  cuts:=wholeCuts r
  lengths:=by
    intro cut hcut
    obtain ⟨cuts,hcuts,hcut⟩:=List.mem_flatten.mp hcut
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hcuts
    exact StagePrint.nativeEqualityCuts_lengths (termRequest r i) cut hcut
  fits:=by
    intro cut hcut
    obtain ⟨cuts,hcuts,hcut⟩:=List.mem_flatten.mp hcut
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hcuts
    rw [←termRequest_width r i]
    exact StageNativeWidth.nativeEqualityCuts_fits (termRequest r i) cut hcut
  square:=wholeCuts_square r

/-- `lem:print`, paper/paper.tex: the complete
native table is computed from the literal original source and actual
expanded Terms, never supplied as a request field or semantic oracle. -/
noncomputable def actualTable {B1 B2 : ℕ} (r : IndexedRequest B1 B2) : StagePrint.TableRequest :=
  (wholeRequest r).table

end NearQuarticWires.StageCertNative
