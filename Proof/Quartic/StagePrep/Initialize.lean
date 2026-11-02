import Proof.Gates.Dispatch.Setup
import Proof.Quartic.StagePrep.IntegerCensus

/-!
# Initialization for the public call computation

Paper: normalized calls in paper/paper.tex and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch

/-- The constants used to parse normalized calls in
`sec:counting`, paper/paper.tex. -/
def initialConstants : St VV :=
  .seq (.op (.inc v1)) (.seq (.op (.inc v2)) (.op (.inc v2)))

/-- The preparation initialization of `prop:time`,
paper/paper.tex, sets the constants without
reading the call or witness. -/
theorem initialConstants_spec (C : Ctx) (hW : 2 < 2 ^ C.Wd) :
    Hs C initialConstants a0 5 (fun b => Cst b ∧ b.cp = 0 ∧
      b.wq = 0 ∧ b.out = [] ∧ Fr a0 b [v1, v2]) := by
  unfold initialConstants
  refine Hs.seq (t2 := 3) (hs_inc C v1 a0 (by change 0 + 1 < 2 ^ C.Wd; omega)) ?_
  rintro b rfl
  refine Hs.seq (t2 := 1) (hs_inc C v2 _ (by
    rw [DS.set_env_ne _ _ (by decide)]; change 0 + 1 < 2 ^ C.Wd; omega)) ?_
  rintro d rfl
  refine Hs.mono (hs_inc C v2 _ (by
    rw [DS.set_env_self, DS.set_env_ne _ _ (by decide)]; change (0 + 1) + 1 < 2 ^ C.Wd; omega)) le_rfl ?_
  rintro e rfl
  refine ⟨⟨?_, ?_, ?_, ?_⟩, rfl, rfl, rfl, ?_⟩
  · simp [a0, DS.set, vZ, v1, v2]
  · simp [a0, DS.set, v1, v2]
  · simp [a0, DS.set, v1, v2]
  · simp [a0, DS.set, vPOS, v1, v2]
  · exact Fr.trans (Fr.set _ _ (by decide))
      (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide)))

/-- The initial wire and unit-top accumulators for
`def:class`, paper/paper.tex. -/
def resetCensus : St VV :=
  .seq (.op (.zero censusTotal)) (.op (.copy censusUnit v1))

/-- Resetting the accumulators of `def:class`, paper/paper.tex takes three steps and reads no input. -/
theorem resetCensus_spec (C : Ctx) (a : DS VV) (hc : Cst a) :
    Hs C resetCensus a 3 (fun b => b.env censusTotal = 0 ∧
      b.env censusUnit = 1 ∧ b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧
      Cst b ∧ Fr a b [censusTotal, censusUnit]) := by
  unfold resetCensus
  refine Hs.seq (t2 := 1) (hs_zero C censusTotal a) ?_
  rintro b rfl
  refine Hs.mono (hs_copy C censusUnit v1 _ (by decide)) le_rfl ?_
  rintro d rfl
  refine ⟨?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
  · rw [DS.set_env_ne _ _ (by decide), DS.set_env_self]
  · rw [DS.set_env_self, DS.set_env_ne _ _ (by decide), hc.one]
  · exact ⟨by rw [DS.set_env_ne _ _ (by decide), DS.set_env_ne _ _ (by decide)]; exact hc.z,
      by rw [DS.set_env_ne _ _ (by decide), DS.set_env_ne _ _ (by decide)]; exact hc.one,
      by rw [DS.set_env_ne _ _ (by decide), DS.set_env_ne _ _ (by decide)]; exact hc.two,
      by rw [DS.set_env_ne _ _ (by decide), DS.set_env_ne _ _ (by decide)]; exact hc.pos⟩
  · exact Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide))

end NearQuarticWires.StagePrep
