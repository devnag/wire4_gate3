import Proof.Quartic.StageGreedyCollector.Entry
import Proof.Quartic.StagePrint.NativeCensus
import Proof.Quartic.StageLift.ResidueBounds
import Proof.Quartic.StageLiftSourceCost.Reserve

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyCollector

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.SourceInterfaces
open NearCubicWires.WireExponent3_5
open NearCubicGates.Close.Tabulator
open StagePrint

/-- `lem:residue` and `sec:params`, paper/paper.tex: every actual modular walk uses its unchanged selected
degree and one prime from the original selected interval. -/
theorem entry_degree_le {B1 B2 : ℕ} (r : GreedyEntry.Request B1 B2) :
    r.degree≤r.source.child.selected.1.Dmax := by
  have hs:=Cells.prepare_spec _ r.source.child.selected.1 r.source.child.selected.2
  have hp : r.source.prime≤r.source.child.selected.1.P := by
    have hm:=r.source.prime_mem
    change r.source.prime∈r.source.child.selected.1.primes at hm
    rw [hs.primes_eq,NearCubicGates.Close.Counter.mem_dyadicPrimes] at hm
    exact hm.1
  exact StageLift.residueDegreeBound_le_Dmax hs r.source.prime hp

/-- `lem:print`, paper/paper.tex: the original
child census bounds one actual equality stream at its exact degree,
without an additional maximum-child factor. -/
theorem entry_cuts_count {B1 B2 : ℕ} (r : GreedyEntry.Request B1 B2) :
    (nativeEqualityCuts r.termRequest).length≤r.source.child.selected.1.Uocc^r.degree := by
  have hs:=Cells.prepare_spec _ r.source.child.selected.1 r.source.child.selected.2
  have hkids : ∀j,(r.rowContext.nativeKids j).length≤r.source.child.selected.1.childCap := by
    intro j
    rw [hs.childCap_eq]
    exact r.rowContext.nativeKids_length_le j hs.n_pos
  have hc:=nativeEqualityCuts_count_le r.termRequest r.source.child.selected.1.childCap hkids
  have hg : (Builder.allGates r.source.child.call).length≤2*r.source.child.call.n^4 := by
    have hh:=hs.input_valid.2.2.1.trans hs.input_valid.2.2.2.1
    simpa only [Builder.callInput,Builder.allGates,List.length_append] using hh
  have hbase : 1+17*(Builder.allGates r.source.child.call).length*r.source.child.selected.1.childCap≤
      r.source.child.selected.1.Uocc := by
    rw [hs.Uocc_eq,hs.NatAtoms_eq,hs.m_eq]
    change 1+17*(Builder.allGates r.source.child.call).length*r.source.child.selected.1.childCap≤
      1+17*(2*r.source.child.call.n^4)*r.source.child.selected.1.childCap
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hg)) 1
  exact hc.trans (Nat.pow_le_pow_left hbase _)

/-- `lem:print` and `sec:params`, paper/paper.tex: every one of the original walk streams satisfies the
selected hundredth-exponent bound, including zero-weight walks. -/
theorem entry_cuts_bound {B1 B2 : ℕ} (r : GreedyEntry.Request B1 B2) :
    (nativeEqualityCuts r.termRequest).length≤
      2^((r.source.child.call.n-r.source.child.selected.1.k)/100) := by
  have hs:=Cells.prepare_spec _ r.source.child.selected.1 r.source.child.selected.2
  have hb:=hs.printing_entries r.degree (entry_degree_le r)
  have hpos : 1≤2^(r.source.child.selected.1.m*r.source.child.selected.1.k) := Nat.one_le_two_pow
  exact (entry_cuts_count r).trans ((Nat.le_mul_of_pos_left _ hpos).trans hb)

/-- `lem:print`, paper/paper.tex: the doubled
cut census of this one walk satisfies the actual native rectangular
capacity, before any global concatenation or modular reduction. -/
theorem entry_cuts_square {B1 B2 : ℕ} (r : GreedyEntry.Request B1 B2) :
    (2*(nativeEqualityCuts r.termRequest).length)*(2*(nativeEqualityCuts r.termRequest).length)≤
      rectangularInnerDimension (2^PrimT.C4Geo.dRow r.rowContext.header.prepared.starParams) := by
  let hs:=Cells.prepare_spec _ r.source.child.selected.1 r.source.child.selected.2
  let free:=r.source.child.call.n-r.source.child.selected.1.k
  let q:=free/100
  have hfree : 200≤free := by
    have h:=hs.initial_degree
    change 100*(r.source.child.selected.1.m*r.source.child.selected.1.k+2+
      0*Nat.clog 2 r.source.child.selected.1.Uocc)≤free at h
    omega
  have hq : 2≤q := (Nat.le_div_iff_mul_le (by decide)).mpr hfree
  have hqmul : 100*q≤free := by
    simpa only [Nat.mul_comm] using Nat.div_mul_le_self free 100
  have hsum:=Builder.centerCount_eq r.source.child.call hs
  have hbalance:=hs.starParams.centerBits_balanced.1
  have hdim : free≤2*PrimT.C4Geo.dRow hs.starParams := by
    change hs.starParams.rightCenterBits≤hs.starParams.leftCenterBits at hbalance
    change free=hs.starParams.leftCenterBits+hs.starParams.rightCenterBits at hsum
    change free≤2*hs.starParams.leftCenterBits
    omega
  have he : 20*(q+1)≤PrimT.C4Geo.dRow hs.starParams := by omega
  have hcount : 2*(nativeEqualityCuts r.termRequest).length≤2^(q+1) := by
    have h:=Nat.mul_le_mul_left 2 (entry_cuts_bound r)
    change 2*(nativeEqualityCuts r.termRequest).length≤2*2^q at h
    simpa only [pow_succ,Nat.mul_comm] using h
  have hp : (2*(nativeEqualityCuts r.termRequest).length)^20≤2^PrimT.C4Geo.dRow hs.starParams := by
    calc
      _≤(2^(q+1))^20 := Nat.pow_le_pow_left hcount _
      _=2^(20*(q+1)) := by rw [←pow_mul,Nat.mul_comm]
      _≤_ := Nat.pow_le_pow_right (by decide) he
  have hh : ((2*(nativeEqualityCuts r.termRequest).length)*(2*(nativeEqualityCuts r.termRequest).length))^10≤
      (rectangularInnerDimension (2^PrimT.C4Geo.dRow hs.starParams))^10 := by
    calc
      _=(2*(nativeEqualityCuts r.termRequest).length)^20 := by ring
      _≤2^PrimT.C4Geo.dRow hs.starParams := hp
      _≤_ := le_integerCeilRoot_pow (by decide : 0<10)
  exact (Nat.pow_le_pow_iff_left (by decide : 10≠0)).mp hh

end NearQuarticWires.StageGreedyCollector
