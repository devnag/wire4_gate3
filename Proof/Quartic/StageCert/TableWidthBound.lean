import Proof.Quartic.StageCert.WidthGuards
import Proof.Quartic.StageCert.RecordBounds
import Proof.Quartic.StageCert.RecordCounts

set_option autoImplicit false

namespace NearQuarticWires.StageCert
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.CounterMachine.CellTablesProg (natBitLength_le_of_lt)

/-- `prop:time`, paper/paper.tex: a field bounded by a
power of two needs at most one further binary place. -/
theorem bitLength_le_of_le_pow (v B : ℕ) (h : v≤2^B) : natBitLength v≤B+1 := by
  have hp : 2^B<2^(B+1) := by rw [pow_succ]; have hp0 : 1≤2^B := Nat.one_le_two_pow; omega
  exact natBitLength_le_of_lt v (B+1) (by omega) (h.trans_lt hp)

/-- `prop:time`, paper/paper.tex: a finite running maximum
is bounded by any bound on its initial value and every actual field. -/
theorem foldMax_le (xs : List ℕ) (a B : ℕ) (ha : a≤B) (h : ∀x∈xs,x≤B) :
    xs.foldl max a≤B := by
  induction xs generalizing a with
  | nil => exact ha
  | cons x xs ih =>
    apply ih (max a x) (max_le ha (h x (by simp)))
    exact fun y hy => h y (by simp [hy])

/-- `prop:time`, paper/paper.tex: the common certificate
width depends on binary moment height and logarithmic column count, never
on the number of columns themselves. -/
theorem tableWidth_le (r : CertTableRequest) (n R K : ℕ)
    (hcols : r.columns.length≤2^n)
    (hlen : ∀rs∈r.columns,rs.length≤R)
    (hrec : ∀rs∈r.columns,∀t∈rs,|t.1|≤(2:ℤ)^K ∧ t.2≤2^K) :
    tableWidth r≤r.payload.length+n+R+K+8 := by
  let B := r.payload.length+n+R+K+4
  have hself (v : ℕ) : natBitLength v≤v+1 :=
    Nat.add_le_add_right (Nat.log_le_self 2 v) 1
  have hfields : ∀v∈scalarFields r,natBitLength v≤B := by
    intro v hv
    simp only [scalarFields,List.mem_cons] at hv
    rcases hv with rfl | rfl | rfl | hv
    · exact (hself _).trans (by dsimp [B]; omega)
    · exact (bitLength_le_of_le_pow _ n hcols).trans (by dsimp [B]; omega)
    · cases r.doAppend <;> norm_num [natBitLength,B]
    · obtain ⟨rs,hrs,hv⟩ := List.mem_flatMap.mp hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact (hself _).trans (by have := hlen rs hrs; dsimp [B]; omega)
      · obtain ⟨t,ht,hv⟩ := List.mem_flatMap.mp hv
        obtain ⟨ha,hb⟩ := hrec rs hrs t ht
        have hn : t.1.natAbs≤2^K := by
          exact_mod_cast (show (t.1.natAbs:ℤ)≤(2:ℤ)^K by simpa only [Int.natCast_natAbs] using ha)
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
        rcases hv with rfl | rfl | rfl
        · split_ifs <;> norm_num [natBitLength,B]
        · exact (bitLength_le_of_le_pow _ K hn).trans (by dsimp [B]; omega)
        · exact (bitLength_le_of_le_pow _ K hb).trans (by dsimp [B]; omega)
  have hmax : ((scalarFields r).map natBitLength).foldl max 0≤B :=
    foldMax_le _ _ _ (by dsimp [B]; omega) (by
      intro v hv
      obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hv
      exact hfields w hw)
  unfold tableWidth
  dsimp [B] at hmax
  omega

end NearQuarticWires.StageCert
