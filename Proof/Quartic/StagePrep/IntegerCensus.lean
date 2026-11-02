import Proof.Gates.Dispatch.Walk
import Proof.Gates.Dispatch.ParseCirc

/-!
# Integer tests for the physical wire census

Paper: `def:class`, paper/paper.tex, and normalized
calls. Input wires are counted by nonzero weights;
the top coefficients must equal one.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open NearCubicWires
open NearCubicGates.Close.Interfaces

/-- The wire accumulator of `def:class`, paper/paper.tex. -/
def censusTotal : Fin VV := ⟨61, by decide⟩

/-- The unit-coefficient flag of normalized calls, `sec:counting`, paper/paper.tex. -/
def censusUnit : Fin VV := ⟨62, by decide⟩

/-- The contribution of one input weight in `def:class`,
paper/paper.tex. -/
def wireBit (z : ℤ) : ℕ := if z = 0 then 0 else 1

/-- The signed integer reader followed by the nonzero test of
`def:class`, paper/paper.tex. -/
def countWeight : St VV := .seq readInt
  (.ite (.eq t3 vZ) skipS (.op (.inc censusTotal)))

/-- The wire test of `def:class`, paper/paper.tex,
adds precisely one for a nonzero input weight. -/
theorem countWeight_spec (C : Ctx) (a : DS VV) (hc : Cst a)
    (z : ℤ) (rest : List Bool)
    (hcw : C.cw.drop a.cp = intWord z ++ rest)
    (hW : C.cw.length + 2 ≤ C.Wd) (hL : C.cw.length + 2 < 2 ^ C.Wd)
    (htotal : a.env censusTotal + 1 < 2 ^ C.Wd) :
    Hs C countWeight a (60 * (intWord z).length + 73) (fun b =>
      b.env censusTotal = a.env censusTotal + wireBit z ∧
      b.cp = a.cp + (intWord z).length ∧ b.wq = a.wq ∧ b.out = a.out ∧
      Cst b ∧ Fr a b (censusTotal :: readIntT)) := by
  unfold countWeight
  refine Hs.seq (t2 := 2) (readInt_spec a hc z rest hcw hW hL) ?_
  rintro b ⟨_, hb3, _, hbcp, hbwq, hbout, hbc, hbfr⟩
  have hbt : b.env censusTotal = a.env censusTotal := hbfr _ (by decide)
  refine Hs.ite (c := .eq t3 vZ) (show t3 ≠ vZ by decide) ?_ ?_
  · intro he
    have hz : z = 0 := by
      simp only [Cnd.eval, hb3, hbc.z, decide_eq_true_eq] at he
      omega
    refine Hs.mono (skip_spec b) le_rfl ?_
    rintro d rfl
    refine ⟨?_, hbcp, hbwq, hbout, ?_, ?_⟩
    · rw [DS.set_env_ne _ _ (by decide), hbt]
      simp [wireBit, hz]
    · exact ⟨by rw [DS.set_env_ne _ _ (by decide)]; exact hbc.z,
        by rw [DS.set_env_ne _ _ (by decide)]; exact hbc.one,
        by rw [DS.set_env_ne _ _ (by decide)]; exact hbc.two,
        by rw [DS.set_env_ne _ _ (by decide)]; exact hbc.pos⟩
    · exact Fr.trans (Fr.weaken hbfr (by decide)) (Fr.set _ _ (by decide))
  · intro he
    have hz : z ≠ 0 := by
      simp only [Cnd.eval, hb3, hbc.z, decide_eq_false_iff_not] at he
      exact fun h => he (by simp [h])
    refine Hs.mono (hs_inc C censusTotal b (by rw [hbt]; exact htotal)) le_rfl ?_
    rintro d rfl
    refine ⟨?_, hbcp, hbwq, hbout, ?_, ?_⟩
    · rw [DS.set_env_self, hbt]
      simp [wireBit, hz]
    · exact ⟨by rw [DS.set_env_ne _ _ (by decide)]; exact hbc.z,
        by rw [DS.set_env_ne _ _ (by decide)]; exact hbc.one,
        by rw [DS.set_env_ne _ _ (by decide)]; exact hbc.two,
        by rw [DS.set_env_ne _ _ (by decide)]; exact hbc.pos⟩
    · exact Fr.trans (Fr.weaken hbfr (by decide)) (Fr.set _ _ (by decide))

/-- The unit-coefficient test of normalized calls, `sec:counting`, paper/paper.tex, checks both the sign and magnitude. -/
def checkUnitCoefficient : St VV := .seq readInt
  (.ite (.eq t8 vZ) (.ite (.eq t3 v1) skipS (.op (.zero censusUnit)))
    (.op (.zero censusUnit)))

/-- The coefficient test of `sec:counting`, paper/paper.tex is the
exact conjunction of its prior flag and the equation `z = 1`. -/
theorem checkUnitCoefficient_spec (C : Ctx) (a : DS VV) (hc : Cst a)
    (z : ℤ) (rest : List Bool) (P : Prop) [Decidable P]
    (hflag : a.env censusUnit = bnat P)
    (hcw : C.cw.drop a.cp = intWord z ++ rest)
    (hW : C.cw.length + 2 ≤ C.Wd) (hL : C.cw.length + 2 < 2 ^ C.Wd) :
    Hs C checkUnitCoefficient a (60 * (intWord z).length + 74) (fun b =>
      b.env censusUnit = bnat (P ∧ z = 1) ∧
      b.cp = a.cp + (intWord z).length ∧ b.wq = a.wq ∧ b.out = a.out ∧
      Cst b ∧ Fr a b (censusUnit :: readIntT)) := by
  unfold checkUnitCoefficient
  refine Hs.seq (t2 := 3) (readInt_spec a hc z rest hcw hW hL) ?_
  rintro b ⟨hb8, hb3, _, hbcp, hbwq, hbout, hbc, hbfr⟩
  have hbf : b.env censusUnit = bnat P := (hbfr _ (by decide)).trans hflag
  have hzero : Hs C (.op (.zero censusUnit)) b 1 (fun d =>
      d.env censusUnit = 0 ∧ d.cp = b.cp ∧ d.wq = b.wq ∧ d.out = b.out ∧
      Cst d ∧ Fr b d [censusUnit, vJ]) := by
    refine Hs.mono (hs_zero C censusUnit b) le_rfl ?_
    rintro d rfl
    exact ⟨by simp, rfl, rfl, rfl,
      ⟨by rw [DS.set_env_ne _ _ (by decide)]; exact hbc.z,
       by rw [DS.set_env_ne _ _ (by decide)]; exact hbc.one,
       by rw [DS.set_env_ne _ _ (by decide)]; exact hbc.two,
       by rw [DS.set_env_ne _ _ (by decide)]; exact hbc.pos⟩,
      Fr.set _ _ (by decide)⟩
  have hfinish : ∀ (d : DS VV), d.env censusUnit = bnat (P ∧ z = 1) →
      d.cp = b.cp → d.wq = b.wq → d.out = b.out → Cst d →
      Fr b d [censusUnit, vJ] →
      d.env censusUnit = bnat (P ∧ z = 1) ∧
      d.cp = a.cp + (intWord z).length ∧ d.wq = a.wq ∧ d.out = a.out ∧
      Cst d ∧ Fr a d (censusUnit :: readIntT) := by
    intro d hf hp hw ho hconst hfr
    exact ⟨hf, hp.trans hbcp, hw.trans hbwq, ho.trans hbout, hconst,
      Fr.trans (Fr.weaken hbfr (by decide)) (Fr.weaken hfr (by decide))⟩
  refine Hs.ite (c := .eq t8 vZ) (show t8 ≠ vZ by decide) ?_ ?_
  · intro hs
    have hznonneg : 0 ≤ z := by
      simp only [Cnd.eval, hb8, hbc.z, decide_eq_true_eq] at hs
      split_ifs at hs
      omega
    refine Hs.ite (c := .eq t3 v1) (show t3 ≠ v1 by decide) ?_ ?_
    · intro hm
      have hz : z = 1 := by
        simp only [Cnd.eval, hb3, hbc.one, decide_eq_true_eq] at hm
        omega
      refine Hs.mono (skip_spec b) le_rfl ?_
      rintro d rfl
      apply hfinish
      · rw [DS.set_env_ne _ _ (by decide), hbf]
        simp [hz]
      · rfl
      · rfl
      · rfl
      · exact ⟨by rw [DS.set_env_ne _ _ (by decide)]; exact hbc.z,
          by rw [DS.set_env_ne _ _ (by decide)]; exact hbc.one,
          by rw [DS.set_env_ne _ _ (by decide)]; exact hbc.two,
          by rw [DS.set_env_ne _ _ (by decide)]; exact hbc.pos⟩
      · exact Fr.set _ _ (by decide)
    · intro hm
      have hz : z ≠ 1 := by
        simp only [Cnd.eval, hb3, hbc.one, decide_eq_false_iff_not] at hm
        exact fun h => hm (by simp [h])
      refine Hs.mono hzero le_rfl ?_
      rintro d ⟨hf, hp, hw, ho, hconst, hfr⟩
      exact hfinish d (by simp [hf, bnat, hz]) hp hw ho hconst hfr
  · intro hs
    have hz : z ≠ 1 := by
      simp only [Cnd.eval, hb8, hbc.z, decide_eq_false_iff_not] at hs
      exact fun h => hs (by simp [h])
    refine Hs.mono hzero (by omega) ?_
    rintro d ⟨hf, hp, hw, ho, hconst, hfr⟩
    exact hfinish d (by simp [hf, bnat, hz]) hp hw ho hconst hfr

end NearQuarticWires.StagePrep
