import Proof.Quartic.StagePrint.GreedyNativeTarget
import Proof.Quartic.StageGreedyCollector.EntryBounds

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyNativeData

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.SourceInterfaces
open NearCubicWires.WireExponent3_5
open StagePrint
open scoped BigOperators

/-- `lem:print`, paper/paper.tex: all original
low-first walks contribute their literal equality occurrences. -/
noncomputable def equalityCuts {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :=
  (List.ofFn fun i : Fin (r.child.cellCall.seed.N^8) =>
    nativeEqualityCuts (GreedyEntry.Request.termRequest ⟨r,i⟩)).flatten

/-- `lem:print` and `sec:params`, paper/paper.tex: the global first-moment census retains the original
selected degree and the original hundredth-exponent reserve. -/
theorem equalityCuts_count {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    (equalityCuts r).length ≤
      2^((r.child.call.n-r.child.selected.1.k)/100) := by
  let hs:=Cells.prepare_spec _ r.child.selected.1 r.child.selected.2
  let D:=StageLift.residueDegreeBound r.child.selected.1 r.prime
  have hD:=StageGreedyCollector.entry_degree_le
    (GreedyEntry.Request.mk r ⟨0,StageLiftSourceCost.walkCount_pos r⟩)
  have hm:=StageLiftSourceCost.walkCount_le r
  rw [←hs.m_eq] at hm
  have hsum : (equalityCuts r).length ≤
      r.child.cellCall.seed.N^8*r.child.selected.1.Uocc^D := by
    simp only [equalityCuts,List.length_flatten,List.map_ofFn,Function.comp_def,List.sum_ofFn]
    calc
      _ ≤ ∑ i : Fin (r.child.cellCall.seed.N^8),r.child.selected.1.Uocc^D := by
        apply Finset.sum_le_sum
        intro i _
        exact StageGreedyCollector.entry_cuts_count ⟨r,i⟩
      _ = _ := by simp
  exact hsum.trans ((Nat.mul_le_mul_right _ hm).trans (hs.printing_entries D hD))

/-- `lem:print`, paper/paper.tex: the complete
doubled stream satisfies the native degree-ten rectangular root,
including all zero-coefficient occurrences. -/
theorem equalityCuts_square {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    (2*(equalityCuts r).length)*(2*(equalityCuts r).length) ≤
      rectangularInnerDimension (2^PrimT.C4Geo.dRow (GreedyCollector.star r)) := by
  let hs:=Cells.prepare_spec _ r.child.selected.1 r.child.selected.2
  let free:=r.child.call.n-r.child.selected.1.k
  let q:=free/100
  have hfree : 200 ≤ free := by
    have h:=hs.initial_degree
    change 100*(r.child.selected.1.m*r.child.selected.1.k+2+
      0*Nat.clog 2 r.child.selected.1.Uocc) ≤ free at h
    omega
  have hq : 2 ≤ q := (Nat.le_div_iff_mul_le (by decide)).mpr hfree
  have hqmul : 100*q ≤ free := by
    simpa only [Nat.mul_comm] using Nat.div_mul_le_self free 100
  have hsum:=Builder.centerCount_eq r.child.call hs
  have hbalance:=hs.starParams.centerBits_balanced.1
  have hdim : free ≤ 2*PrimT.C4Geo.dRow hs.starParams := by
    change hs.starParams.rightCenterBits ≤ hs.starParams.leftCenterBits at hbalance
    change free=hs.starParams.leftCenterBits+hs.starParams.rightCenterBits at hsum
    change free ≤ 2*hs.starParams.leftCenterBits
    omega
  have he : 20*(q+1) ≤ PrimT.C4Geo.dRow hs.starParams := by omega
  have hcount : 2*(equalityCuts r).length ≤ 2^(q+1) := by
    have h:=Nat.mul_le_mul_left 2 (equalityCuts_count r)
    simpa only [pow_succ,Nat.mul_comm] using h
  have hp : (2*(equalityCuts r).length)^20 ≤ 2^PrimT.C4Geo.dRow hs.starParams := by
    calc
      _ ≤ (2^(q+1))^20 := Nat.pow_le_pow_left hcount _
      _ = 2^(20*(q+1)) := by rw [←pow_mul,Nat.mul_comm]
      _ ≤ _ := Nat.pow_le_pow_right (by decide) he
  have hh : ((2*(equalityCuts r).length)*(2*(equalityCuts r).length))^10 ≤
      (rectangularInnerDimension (2^PrimT.C4Geo.dRow hs.starParams))^10 := by
    calc
      _ = (2*(equalityCuts r).length)^20 := by ring
      _ ≤ 2^PrimT.C4Geo.dRow hs.starParams := hp
      _ ≤ _ := le_integerCeilRoot_pow (by decide : 0<10)
  exact (Nat.pow_le_pow_iff_left (by decide : 10≠0)).mp hh

end NearQuarticWires.StageGreedyNativeData
