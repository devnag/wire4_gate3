import Proof.Quartic.StagePrint.NativeWidthInterface
import Proof.Quartic.StagePullback.NativeFields

set_option autoImplicit false

namespace NearQuarticWires.StageNativeWidth

open NearCubicWires NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.WordPrograms
open StagePullback StagePullback.NativeRows

/-- `lem:print`, paper/paper.tex: the actual signed
low-sign-bit codec bounds the corresponding magnitude. -/
theorem natAbs_le_encS (z : ℤ) : z.natAbs ≤ SInt.encS z := by
  unfold SInt.encS
  split_ifs <;> omega

/-- `imp:pullback`, paper/paper.tex: the exact affine
target correction's magnitude is bounded by its selected original mass. -/
theorem targetPrefix_abs_le_mass (q : PointRequest) (e : ExactThresholdGate q.parameters.n)
    (k : ℕ) : (targetPrefix q e k).natAbs ≤ massPrefix q e k := by
  induction k with
  | zero => simp [targetPrefix, massPrefix]
  | succ k ih =>
    rw [targetPrefix_succ, massPrefix_succ]
    have h := Int.natAbs_add_le (targetPrefix q e k)
      (if coordinateFlip q k then originalWeight q e k else 0)
    split_ifs at h ⊢ <;> (try simp only [Int.natAbs_zero] at h) <;> omega

/-- `imp:pullback` and `lem:print`, paper/paper.tex: the six-bit source slack covers the exact adjusted signed
target and all routed original coefficients, without a machine-width premise. -/
theorem sourceSlack (n L : ℕ) (z : ℤ) (hz : z.natAbs ≤ (n + 1) * 2^L) :
    SInt.encS z < 2^(L + n + 6) := by
  have hn : n + 1 ≤ 2^n := Nat.lt_two_pow_self
  have hmag : z.natAbs ≤ 2^(L+n) := by
    calc
      _ ≤ (n+1) * 2^L := hz
      _ ≤ 2^n * 2^L := Nat.mul_le_mul_right _ hn
      _ = _ := by rw [← pow_add, Nat.add_comm]
  have hp : 0 < 2^(L+n) := Nat.two_pow_pos _
  rw [pow_add]
  norm_num only [Nat.reducePow]
  unfold SInt.encS
  split_ifs <;> omega

/-- `imp:pullback`, paper/paper.tex: routing only
changes an original coefficient's sign; zero padding adds no magnitude. -/
theorem route_pad_abs {n : ℕ} (e : ExactThresholdGate n) (side flips : List Bool)
    (width A : ℕ) (h : ∀ i, (e.weight i).natAbs ≤ A) :
    ∀ z ∈ Pool.padTo width (Pool.routeL (Pool.coords side flips e)) ++
      Pool.padTo width (Pool.routeR (Pool.coords side flips e)), z.natAbs ≤ A := by
  intro z hz
  have hcoord : ∀ c ∈ Pool.coords side flips e, c.2.2.natAbs ≤ A := by
    intro c hc
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
    exact h i
  have hr : ∀ cs : List Pool.Coord, (∀ c ∈ cs, c.2.2.natAbs ≤ A) →
      ∀ z ∈ cs.map (fun c => Pool.flipW c.2.1 c.2.2), z.natAbs ≤ A := by
    intro cs hh z hz
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hz
    have hb := hh c hc
    unfold Pool.flipW
    split_ifs <;> simpa only [Int.natAbs_neg] using hb
  have hl : ∀ z ∈ Pool.routeL (Pool.coords side flips e), z.natAbs ≤ A :=
    hr _ (fun c hc => hcoord c (List.mem_filter.mp hc).1)
  have hrr : ∀ z ∈ Pool.routeR (Pool.coords side flips e), z.natAbs ≤ A :=
    hr _ (fun c hc => hcoord c (List.mem_filter.mp hc).1)
  simp only [Pool.padTo, List.mem_append] at hz
  rcases hz with (hz | hz) | (hz | hz)
  · exact hl z hz
  · have he : z = 0 := List.eq_of_mem_replicate hz
    simp [he]
  · exact hrr z hz
  · have he : z = 0 := List.eq_of_mem_replicate hz
    simp [he]

end NearQuarticWires.StageNativeWidth
