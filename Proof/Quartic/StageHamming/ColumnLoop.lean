import Proof.Quartic.StageHamming.ColumnStep

set_option autoImplicit false

namespace NearQuarticWires.StageHamming

open NearCubicGates.Close.Cells

def columnLoopScratch : List (Fin VV) := columnCounter :: columnStepScratch

/-- `imp:partition`, paper/paper.tex: the original
codeword-column bit is accumulated over the actual check coordinates. -/
def columnLoop : St VV MM := forS columnCounter parityWidth columnStep

/-- `imp:partition` and `prop:time`, paper/paper.tex: the physical check-coordinate scan produces the exact
canonical column bit within a quadratic code-width clock. -/
theorem columnLoop_spec {C : Ctx} (a : DS VV MM) (hc : Cst a)
    (i q s : ℕ) (hinput : a.env bitInput = i + 1)
    (hsucc : a.env paritySuccessor = q + 1) (hswidth : a.env parityWidth = s)
    (hpower : a.env parityPower = 1) (hflag : a.env columnOutput = (q == i).toNat)
    (hs : s < 2 ^ C.Wd) (hwidth : 2 ≤ C.Wd) (hW : 2 ^ s < 2 ^ C.Wd) :
    Hs C columnLoop a (s * (5 * s + 21) + 4) (fun b =>
      b.env parityPower = 2 ^ s ∧
      b.env columnOutput = (columnPrefix i q s).toNat ∧
      b.sh = a.sh ∧ Fr a b columnLoopScratch) := by
  let Inv : ℕ → DS VV MM → Prop := fun k b =>
    b.env parityPower = 2 ^ k ∧ b.env columnOutput = (columnPrefix i q k).toNat ∧
      b.env bitInput = i + 1 ∧ b.env paritySuccessor = q + 1 ∧ b.sh = a.sh ∧
      Fr a b columnLoopScratch
  have hloop := forS_spec' (C := C) columnCounter parityWidth (by decide)
    columnStep a s hs Inv (5 * s + 17)
    (fun k b v hb => by
      obtain ⟨hp, hf, hi, hq, hsh, hfr⟩ := hb
      exact ⟨(DS.set_env_ne _ _ (by decide)).trans hp,
        (DS.set_env_ne _ _ (by decide)).trans hf,
        (DS.set_env_ne _ _ (by decide)).trans hi,
        (DS.set_env_ne _ _ (by decide)).trans hq,
        hsh, hfr.trans (Fr.set _ _ (by simp [columnLoopScratch]))⟩)
    (by exact ⟨by simpa using hpower, by simpa [columnPrefix] using hflag,
      hinput, hsucc, rfl, Fr.refl _ _⟩) hswidth ?_
  · refine hloop.mono (by apply le_of_eq; ring) ?_
    rintro b ⟨⟨hp, hf, _, _, hsh, hfr⟩, _, _⟩
    exact ⟨hp, hf, hsh, hfr⟩
  · intro k hk b hb hcounter hlimit
    obtain ⟨hp, hf, hi, hq, hsh, hfr⟩ := hb
    have hcb : Cst b := hc.of_fr hfr (by decide)
    refine (columnStep_spec b hcb i q k hi hq hcounter hp hf
      (by omega) hwidth
      ((Nat.pow_le_pow_right (by norm_num) (by omega : k + 1 ≤ s)).trans_lt hW)).mono
      (by omega) ?_
    rintro d ⟨dp, df, dsh, dfr⟩
    exact ⟨⟨dp, df, (dfr _ (by decide)).trans hi,
      (dfr _ (by decide)).trans hq, dsh.trans hsh,
      hfr.trans (dfr.weaken (by decide))⟩,
      (dfr _ (by decide)).trans hcounter, (dfr _ (by decide)).trans hlimit⟩

/-- `imp:partition`, paper/paper.tex: the systematic
data-coordinate contribution is initialized by one actual comparison. -/
def columnInitialFlag : St VV MM :=
  .ite (.eq columnTarget columnData) (.op (.copy columnOutput v1)) (.op (.zero columnOutput))

/-- `imp:partition`, paper/paper.tex: the initialized
column bit is exactly the equality of its original target and data
coordinates, with no incoming flag assumption. -/
theorem columnInitialFlag_spec {C : Ctx} (a : DS VV MM) (hc : Cst a)
    (i q : ℕ) (hi : a.env columnData = i) (hq : a.env columnTarget = q) :
    Hs C columnInitialFlag a 2 (fun b =>
      b.env columnOutput = (q == i).toNat ∧ b.sh = a.sh ∧ Fr a b [columnOutput]) := by
  unfold columnInitialFlag
  refine Hs.ite (c := .eq columnTarget columnData)
    (show columnTarget ≠ columnData by decide) ?_ ?_
  · intro he
    have heq : q = i := by simpa only [Cnd.eval, hi, hq, decide_eq_true_eq] using he
    refine Hs.mono (hs_copy C columnOutput v1 a (by decide)) le_rfl ?_
    rintro b rfl
    exact ⟨by simp [hc.one, heq], rfl, Fr.set _ _ (by simp)⟩
  · intro he
    have hne : q ≠ i := by simpa only [Cnd.eval, hi, hq, decide_eq_false_iff_not] using he
    have hbeq : (q == i) = false := by simp [hne]
    refine Hs.mono (hs_zero C columnOutput a) le_rfl ?_
    rintro b rfl
    exact ⟨by simp [hbeq], rfl, Fr.set _ _ (by simp)⟩

end NearQuarticWires.StageHamming
