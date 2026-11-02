import Proof.Quartic.StageMainMask.PointPrefix
import Proof.Gates.Cells.Arith

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open StagePullback

/-- `imp:partition` and Step 4 of `sec:algorithm`, paper/paper.tex: the point accumulator and binary place
are retained outside every canonical-center and affine-bit register. -/
def packedPointRegister : Fin VV := 64
def packedPointPower : Fin VV := 65

/-- `imp:partition`, paper/paper.tex: the actual
computed coordinate controls one physical binary accumulator addition. -/
def addPointBit : St VV MM :=
  .ite (.eq Flips.accumulator v1) (.op (.add packedPointRegister packedPointPower)) skipS

/-- `imp:partition` and `prop:time`, paper/paper.tex: the actual Boolean coordinate is accumulated exactly,
preserving every source field and paying both branch operations. -/
theorem addPointBit_run (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (bit : Bool) (hbit : a.env Flips.accumulator = bit.toNat)
    (hfit : a.env packedPointRegister + a.env packedPointPower < 2 ^ C.Wd) :
    Hs C addPointBit a 2 (fun b =>
      b.env packedPointRegister = a.env packedPointRegister + bit.toNat * a.env packedPointPower ∧
      b.sh = a.sh ∧ Cst b ∧ Fr a b [packedPointRegister, vJ]) := by
  unfold addPointBit
  refine Hs.ite (c := .eq Flips.accumulator v1)
    (show Flips.accumulator ≠ v1 by decide) ?_ ?_
  · intro he
    have ht : bit = true := by
      revert he
      simp only [Cnd.eval, hbit, hc.one]
      cases bit <;> simp
    refine (hs_add C packedPointRegister packedPointPower a (by decide) hfit).mono le_rfl ?_
    rintro b rfl
    exact ⟨by simp [ht], rfl,
      Cst.of_fr (T := [packedPointRegister, vJ]) hc (Fr.set a _ (by simp)) (by decide),
      Fr.set a _ (by simp)⟩
  · intro he
    have ht : bit = false := by
      revert he
      simp only [Cnd.eval, hbit, hc.one]
      cases bit <;> simp
    refine (skip_spec a).mono le_rfl ?_
    rintro b rfl
    exact ⟨by simp [ht, DS.set_env_ne _ _ (by decide : packedPointRegister ≠ vJ)], rfl,
      Cst.of_fr (T := [packedPointRegister, vJ]) hc (Fr.set a _ (by simp)) (by decide),
      Fr.set a _ (by simp)⟩

/-- `imp:partition`, paper/paper.tex: append a
computed coordinate and advance the retained binary place. -/
def appendPointBit : St VV MM := .seq addPointBit (.op (.shl packedPointPower))

/-- `imp:partition` and `prop:time`, paper/paper.tex: the literal next-coordinate operations produce the
exact next prefix of the original point with constant source clock. -/
theorem appendPointBit_run (C : Ctx) (q : PointRequest) (k : ℕ) (hk : k < q.parameters.n)
    (a : DS VV MM) (hc : Cst a)
    (hbit : a.env Flips.accumulator = (q.point ⟨k, hk⟩).toNat)
    (hv : a.env packedPointRegister = pointPrefix q k)
    (hp : a.env packedPointPower = 2 ^ k) (hwidth : q.parameters.n + 4 ≤ C.Wd) :
    Hs C appendPointBit a 4 (fun b =>
      b.env packedPointRegister = pointPrefix q (k + 1) ∧
      b.env packedPointPower = 2 ^ (k + 1) ∧ b.sh = a.sh ∧ Cst b ∧
      Fr a b [packedPointRegister, packedPointPower, vJ]) := by
  have hpow : 2 ^ (k + 1) < 2 ^ C.Wd := Nat.pow_lt_pow_right (by decide) (by omega)
  have hfit : a.env packedPointRegister + a.env packedPointPower < 2 ^ C.Wd := by
    rw [hv, hp]
    have hh := pointPrefix_lt q k
    have heq : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; omega
    omega
  unfold appendPointBit
  refine Hs.seq (t1 := 2) (t2 := 1) (addPointBit_run C a hc _ hbit hfit) ?_
  rintro b ⟨hbv, hbsh, hbc, hbfr⟩
  have hbp : b.env packedPointPower = 2 ^ k := (hbfr _ (by decide)).trans hp
  refine (hs_shl C packedPointPower b (by rw [hbp]; simpa [pow_succ, Nat.mul_comm] using hpow)).mono le_rfl ?_
  rintro d rfl
  refine ⟨?_, by simp [hbp, pow_succ, Nat.mul_comm], hbsh,
    hbc.of_fr (T := [packedPointRegister, packedPointPower, vJ])
      (Fr.set b _ (by simp)) (by decide),
    (hbfr.weaken (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto)).trans
      (Fr.set b _ (by simp))⟩
  rw [DS.set_env_ne _ _ (by decide : packedPointRegister ≠ packedPointPower), hbv, hv, hp,
    pointPrefix_succ q k hk]

end NearQuarticWires.StageMainMask
