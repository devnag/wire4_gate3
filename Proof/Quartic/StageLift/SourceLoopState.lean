import Proof.Quartic.StageLift.CarrierStartup

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires NearCubicGates.Close.Cells

/-- Step 3, `sec:algorithm`, paper/paper.tex: the logical entry
record keeps all actual original sources and header fields while the
walk counter and Gamma cursor are tracked separately by the loop. -/
noncomputable def sourceEntryView {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) (a : DS VV MM) : DS VV MM :=
  { a with env := Function.update a.env printWalkIndex 0, rc := Function.update a.rc gammaStore (gammaByteCursor r 0) }

/-- Step 3 and `lem:print`, paper/paper.tex: original retained sources persist through every actual
walk. Register54 is the physical forS counter; its own fit is supplied
by the current ordinal, independently of all other validity fields. -/
structure WalkSourceState {B1 B2 : ℕ} (C : Ctx) (r : Greedy.PrintRequest B1 B2)
    (cursor : ℕ) (a : DS VV MM) : Prop where
  sources : CarrierStartData r (sourceEntryView r a)
  gammaCursor : a.rc gammaStore = gammaByteCursor r cursor
  constants : Cst a
  validExceptCounter : Valid C (a.set printWalkIndex 0)
  inputEmpty : a.kin = []

/-- `prop:time`, paper/paper.tex: setting a
single known-fitting arithmetic register preserves actual validity. -/
theorem source_valid_set {C : Ctx} {a : DS VV MM} (ha : Valid C a)
    (x : Fin VV) (value : ℕ) (hv : value < 2 ^ C.Wd) : Valid C (a.set x value) := by
  refine ⟨fun y => ?_, ha.ip_le, ha.ram_lt, ha.rc_le, ha.kin_le, ha.kout_le, ha.kc_le⟩
  by_cases hy : y = x
  · subst y
    simpa using hv
  · rw [DS.set_env_ne _ _ hy]
    exact ha.env_lt y

/-- Step 3, `sec:algorithm`, paper/paper.tex: replacing a register
by its previous actual value restores the exact original state. -/
theorem source_counter_restore (a : DS VV MM) :
    (a.set printWalkIndex 0).set printWalkIndex (a.env printWalkIndex) = a := by
  cases a
  simp only [DS.set, Function.update_idem, Function.update_eq_self]

/-- Step 3 and `prop:time`, paper/paper.tex: the real bounded walk ordinal restores full validity
at the body entry, without a bound on the Gamma table's byte length. -/
theorem WalkSourceState.valid {B1 B2 : ℕ} {C : Ctx} {r : Greedy.PrintRequest B1 B2}
    {cursor : ℕ} {a : DS VV MM} (ha : WalkSourceState C r cursor a)
    (hcounter : a.env printWalkIndex < 2 ^ C.Wd) : Valid C a := by
  have h := source_valid_set ha.validExceptCounter printWalkIndex (a.env printWalkIndex) hcounter
  rwa [source_counter_restore] at h

/-- Step 3, `sec:algorithm`, paper/paper.tex: the loop invariant
is stable under forS's actual counter assignment; no arbitrary new
counter value is silently assumed to fit the arithmetic width. -/
theorem WalkSourceState.setCounter {B1 B2 : ℕ} {C : Ctx} {r : Greedy.PrintRequest B1 B2}
    {cursor : ℕ} {a : DS VV MM} (ha : WalkSourceState C r cursor a) (value : ℕ) :
    WalkSourceState C r cursor (a.set printWalkIndex value) := by
  refine ⟨?_, ha.gammaCursor, ?_, ?_, ha.inputEmpty⟩
  · simpa only [sourceEntryView, DS.set, Function.update_idem] using ha.sources
  · exact Cst.of_fr ha.constants (Fr.set (T := [printWalkIndex]) a value (by simp)) (by decide)
  · simpa only [DS.set, Function.update_idem] using ha.validExceptCounter

/-- Step 3 and `lem:print`, paper/paper.tex: the actual cold startup establishes the all-walk
source invariant at its physically decoded first Gamma field. -/
theorem WalkSourceState.of_start {B1 B2 : ℕ} {C : Ctx} {r : Greedy.PrintRequest B1 B2}
    {a : DS VV MM} (hs : CarrierStartData r a) (hc : Cst a) (hv : Valid C a)
    (hkin : a.kin = []) : WalkSourceState C r 0 a := by
  have hview : sourceEntryView r a = a := by
    have he : Function.update a.env printWalkIndex 0 = a.env := by
      rw [← hs.walkIndex, Function.update_eq_self]
    have hr : Function.update a.rc gammaStore (gammaByteCursor r 0) = a.rc := by
      rw [← hs.gammaCursor, Function.update_eq_self]
    unfold sourceEntryView
    rw [he, hr]
  refine ⟨by rw [hview]; exact hs, hs.gammaCursor, hc,
    source_valid_set hv printWalkIndex 0 (Nat.two_pow_pos _), hkin⟩

end NearQuarticWires.StageLift
