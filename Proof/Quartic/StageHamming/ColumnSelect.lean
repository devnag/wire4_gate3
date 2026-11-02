import Proof.Quartic.StageHamming.ColumnPrefix

set_option autoImplicit false

namespace NearQuarticWires.StageHamming

open NearCubicGates.Close.Cells

def columnData : Fin VV := 100
def columnTarget : Fin VV := 101
def columnOutput : Fin VV := 102
def columnCounter : Fin VV := 103

def columnSelectScratch : List (Fin VV) := [columnOutput, vJ]

/-- `imp:partition`, paper/paper.tex: a parity
contribution sets the output precisely when its data bit is present
and its original target coordinate is the current power of two. -/
def columnSelect : St VV MM :=
  .ite (.eq bitOutput v1)
    (.ite (.eq paritySuccessor parityPower) (.op (.copy columnOutput v1)) skipS) skipS

/-- `imp:partition` and `prop:time`, paper/paper.tex: the scalar column selection realizes the exact Boolean
update by comparisons and a constant copy, preserving all other data. -/
theorem columnSelect_spec {C : Ctx} (a : DS VV MM) (hc : Cst a)
    (successor power : ℕ) (old bit : Bool)
    (hsucc : a.env paritySuccessor = successor) (hpower : a.env parityPower = power)
    (hflag : a.env columnOutput = old.toNat) (hbit : a.env bitOutput = bit.toNat) :
    Hs C columnSelect a 3 (fun b =>
      b.env columnOutput = (old || (bit && successor == power)).toNat ∧
      b.sh = a.sh ∧ Fr a b columnSelectScratch) := by
  cases bit with
  | false =>
    unfold columnSelect
    refine Hs.mono (Hs.iteF (show bitOutput ≠ v1 by decide)
      (by simp [Cnd.eval, hbit, hc.one]) (skip_spec a)) (by omega) ?_
    rintro b rfl
    exact ⟨by simpa only [DS.set_env_ne _ _ (by decide : columnOutput ≠ vJ),
      Bool.false_and, Bool.or_false] using hflag, rfl, Fr.set _ _ (by simp [columnSelectScratch])⟩
  | true =>
    unfold columnSelect
    refine Hs.iteT (show bitOutput ≠ v1 by decide)
      (by simp [Cnd.eval, hbit, hc.one]) ?_
    refine Hs.ite (c := .eq paritySuccessor parityPower)
      (show paritySuccessor ≠ parityPower by decide) ?_ ?_
    · intro he
      have heq : successor = power := by
        simpa only [Cnd.eval, hsucc, hpower, decide_eq_true_eq] using he
      refine Hs.mono (hs_copy C columnOutput v1 a (by decide)) le_rfl ?_
      rintro b rfl
      exact ⟨by simp [DS.set_env_self, hc.one, heq], rfl,
        Fr.set _ _ (by simp [columnSelectScratch])⟩
    · intro he
      have hne : successor ≠ power := by
        simpa only [Cnd.eval, hsucc, hpower, decide_eq_false_iff_not] using he
      have hbeq : (successor == power) = false := by simp [hne]
      refine Hs.mono (skip_spec a) le_rfl ?_
      rintro b rfl
      refine ⟨?_, rfl, Fr.set _ _ (by simp [columnSelectScratch])⟩
      rw [DS.set_env_ne _ _ (by decide), hflag]
      simp only [Bool.true_and, hbeq, Bool.or_false]

end NearQuarticWires.StageHamming
