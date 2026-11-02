import Proof.Quartic.StagePrint.PoolStateStep

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint
open NearCubicWires NearCubicWires.RepairOrdinary

/-- `lem:print`, paper/paper.tex: all original occurrences use the same actual retained source and one uniform indexed child program. -/
structure PoolFamily (Request : Type) (input : Request→List Bool) where
  count : ℕ
  source : List Bool
  request : Fin count→Request
  indexed : ∀j,input (request j)=NearCubicWires.RepairRepresentation.natWord j.val++source

/-- `lem:print`, paper/paper.tex: an out-of-range index is never visited by the counted original-occurrence loop. -/
def PoolFamily.caches {Request : Type} {input : Request→List Bool}
    (F : PoolFamily Request input) (cache : Request→List Bool) (j : ℕ) : List Bool :=
  if h : j<F.count then cache (F.request ⟨j,h⟩) else []

/-- `prop:time`, paper/paper.tex: the sum of all concrete occurrence clocks bounds each visited occurrence. -/
def PoolFamily.stepBudget {Request : Type} {input : Request→List Bool}
    (F : PoolFamily Request input) (budget : Request→ℕ) : ℕ :=
  (List.ofFn fun j : Fin F.count=>poolOccurrenceCost j.val F.source.length
    (input (F.request j)).length (budget (F.request j))).sum

/-- `prop:time`, paper/paper.tex: every actual indexed call is included in the loop clock. -/
theorem PoolFamily.step_le {Request : Type} {input : Request→List Bool}
    (F : PoolFamily Request input) (budget : Request→ℕ) (j : Fin F.count) :
    poolOccurrenceCost j.val F.source.length (input (F.request j)).length (budget (F.request j))≤
      F.stepBudget budget := by
  apply List.le_sum_of_mem
  exact List.mem_ofFn.mpr ⟨j,rfl⟩

/-- `lem:print`, paper/paper.tex: a counted prefix of original caches occupies no more cells than the complete cache stream. -/
theorem poolPrefix_length_mono (cache : ℕ→List Bool) {i j : ℕ} (h : i≤j) :
    (poolPrefix cache i).length≤(poolPrefix cache j).length := by
  obtain ⟨d,rfl⟩:=Nat.exists_eq_add_of_le h
  simp [poolPrefix,List.range_add,List.flatMap_append,List.length_append]

/-- `lem:print`, paper/paper.tex: a finite original-occurrence family has an explicit complete reusable-bank capacity. -/
def PoolFamily.capacity {Request : Type} {input : Request→List Bool}
    (F : PoolFamily Request input) (cache : Request→List Bool) (budget : Request→ℕ) : ℕ :=
  100*(F.count+F.source.length+1)+F.stepBudget budget+(poolPrefix (F.caches cache) F.count).length

/-- `prop:time`, paper/paper.tex: occurrence-index bit length is bounded by its actual finite index. -/
theorem pool_index_bits (j : ℕ) : natBitLength j≤j+1 := by
  unfold natBitLength
  have h1:=Nat.log_lt_self 2 (show j+1≠0 by omega)
  have h2:=Nat.log_mono_right (show j≤j+1 by omega) (b:=2)
  omega

/-- `lem:print`, paper/paper.tex: every visited input writer fits the common capacity. -/
theorem PoolFamily.write_cap {Request : Type} {input : Request→List Bool}
    (F : PoolFamily Request input) (cache : Request→List Bool) (budget : Request→ℕ) (j : Fin F.count) :
    j.val+8*natBitLength j.val+4*F.source.length+20≤F.capacity cache budget := by
  have hj:=j.isLt
  have hb:=pool_index_bits j.val
  unfold PoolFamily.capacity
  omega

/-- `lem:print`, paper/paper.tex: every original child computation fits the same reusable-bank capacity. -/
theorem PoolFamily.call_cap {Request : Type} {input : Request→List Bool}
    (F : PoolFamily Request input) (cache : Request→List Bool) (budget : Request→ℕ) (j : Fin F.count) :
    2*(input (F.request j)).length+2+budget (F.request j)≤F.capacity cache budget := by
  have hh:=F.step_le budget j
  unfold poolOccurrenceCost callAppendCost at hh
  unfold PoolFamily.capacity
  omega

/-- `lem:print`, paper/paper.tex: each appended child cache fits within the actual complete original-cache stream. -/
theorem PoolFamily.copy_cap {Request : Type} {input : Request→List Bool}
    (F : PoolFamily Request input) (cache : Request→List Bool) (budget : Request→ℕ) (j : Fin F.count) :
    (poolPrefix (F.caches cache) j.val).length+(frame (F.caches cache j.val)).length+1≤
      F.capacity cache budget := by
  have hh:=poolPrefix_length_mono (F.caches cache) (show j.val+1≤F.count by have:=j.isLt;omega)
  rw [poolPrefix_succ,List.length_append] at hh
  unfold PoolFamily.capacity
  omega

end NearQuarticWires.StagePrint
