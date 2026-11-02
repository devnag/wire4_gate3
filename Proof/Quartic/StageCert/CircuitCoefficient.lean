import Proof.Quartic.StageCert.FinalCoefficient
import Proof.Quartic.StageCert.FrequencyCounts

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicGates.Close.Cells

/-- `sec:cells` and `lem:print`, paper/paper.tex: the selected original circuit is retained as its
literal zero-based bank index. -/
def selectedCircuit : Fin VV := ⟨126,by decide⟩

/-- `lem:print`, paper/paper.tex: an occurrence
outside the selected circuit has both signed summands exactly zero. -/
def clearCoefficientPair : St VV MM :=
  .seq (.op (.zero linearPositive)) (.op (.zero linearNegative))

/-- `lem:print` and `prop:time`, paper/paper.tex: zero coefficients are written by actual bounded
operations, retaining all original source records and token output. -/
theorem clearCoefficientPair_run (C : Ctx) (a : DS VV MM) (hc : Cst a) :
    Hs C clearCoefficientPair a 3 (fun z=>z.env linearPositive=0 ∧
      z.env linearNegative=0 ∧ z.sh=a.sh ∧ Cst z ∧
      Fr a z [linearPositive,linearNegative]) := by
  unfold clearCoefficientPair
  refine Hs.seq (t1 := 1) (t2 := 1) (hs_zero C linearPositive a) ?_
  rintro b rfl
  refine (hs_zero C linearNegative _).mono le_rfl ?_
  rintro z rfl
  exact ⟨by rw [DS.set_env_ne _ _ (by decide),DS.set_env_self],by rw [DS.set_env_self],rfl,
    Cst.of_fr (T := [linearPositive,linearNegative]) hc
      ((Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp))) (by decide),
    (Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp))⟩

/-- `sec:cells` and `lem:print`, paper/paper.tex: filter by the physically retained first-bank boundary,
without changing the concatenated original occurrence numbering. -/
def zeroOutsideCircuit : St VV MM :=
  .ite (.eq selectedCircuit vZ)
    (.ite (.lt atomOccurrence firstGateCount) skipS clearCoefficientPair)
    (.ite (.lt atomOccurrence firstGateCount) clearCoefficientPair skipS)

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual circuit index and original bank boundary
produce exactly the zero extension of its signed occurrence weights.
No selected-subbank oracle or change of atom numbering is used. -/
theorem zeroOutsideCircuit_run (C : Ctx) (circuit firstCount g positive negative : ℕ)
    (a : DS VV MM) (hc : Cst a) (hj : a.env selectedCircuit=circuit)
    (hf : a.env firstGateCount=firstCount) (hg : a.env atomOccurrence=g)
    (hp : a.env linearPositive=positive) (hn : a.env linearNegative=negative) :
    Hs C zeroOutsideCircuit a 5 (fun z=>
      z.env linearPositive=(if (if circuit=0 then g<firstCount else firstCount≤g) then positive else 0) ∧
      z.env linearNegative=(if (if circuit=0 then g<firstCount else firstCount≤g) then negative else 0) ∧
      z.sh=a.sh ∧ Cst z ∧ Fr a z [linearPositive,linearNegative,vJ]) := by
  let active : Prop := if circuit=0 then g<firstCount else firstCount≤g
  let R : DS VV MM→Prop := fun z=>
    z.env linearPositive=(if active then positive else 0) ∧
    z.env linearNegative=(if active then negative else 0) ∧
    z.sh=a.sh ∧ Cst z ∧ Fr a z [linearPositive,linearNegative,vJ]
  have keep (ha : active) : Hs C skipS a 3 R := by
    refine (skip_spec a).mono (by omega) ?_
    rintro z rfl
    exact ⟨by rw [if_pos ha,DS.set_env_ne _ _ (by decide)]; exact hp,
      by rw [if_pos ha,DS.set_env_ne _ _ (by decide)]; exact hn,rfl,
      Cst.of_fr (T := [vJ]) hc (Fr.set _ _ (by simp)) (by decide),
      Fr.set _ _ (by simp)⟩
  have clear (ha : ¬active) : Hs C clearCoefficientPair a 3 R := by
    refine (clearCoefficientPair_run C a hc).mono le_rfl ?_
    rintro z ⟨zp,zn,zs,zc,zfr⟩
    exact ⟨by simpa only [if_neg ha] using zp,by simpa only [if_neg ha] using zn,
      zs,zc,zfr.weaken (by simp)⟩
  unfold zeroOutsideCircuit
  refine Hs.ite (t := 4) (c := .eq selectedCircuit vZ)
    (show selectedCircuit≠vZ by decide) ?_ ?_
  · intro he
    have hj0 : circuit=0 := by simpa only [Cnd.eval,hj,hc.z,decide_eq_true_eq] using he
    refine Hs.ite (t := 3) (c := .lt atomOccurrence firstGateCount)
      (show atomOccurrence≠firstGateCount by decide) ?_ ?_
    · intro hl
      apply keep
      simpa only [active,hj0,ite_true,Cnd.eval,hg,hf,decide_eq_true_eq] using hl
    · intro hl
      apply clear
      simpa only [active,hj0,ite_true,Cnd.eval,hg,hf,decide_eq_false_iff_not] using hl
  · intro he
    have hj0 : circuit≠0 := by simpa only [Cnd.eval,hj,hc.z,decide_eq_false_iff_not] using he
    refine Hs.ite (t := 3) (c := .lt atomOccurrence firstGateCount)
      (show atomOccurrence≠firstGateCount by decide) ?_ ?_
    · intro hl
      apply clear
      have hh : g<firstCount := by simpa only [Cnd.eval,hg,hf,decide_eq_true_eq] using hl
      simpa only [active,if_neg hj0,not_le] using hh
    · intro hl
      apply keep
      have hh : ¬g<firstCount := by simpa only [Cnd.eval,hg,hf,decide_eq_false_iff_not] using hl
      simpa only [active,if_neg hj0,not_lt] using hh

end NearQuarticWires.StageCert.Tokens
