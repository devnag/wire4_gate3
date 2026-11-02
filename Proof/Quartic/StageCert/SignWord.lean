import Proof.Quartic.StageCert.PolarityToken

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicGates.Close.Cells

/-- `sec:walks` and `lem:print`, paper/paper.tex: remaining low-first bits of the original sign ordinal. -/
def remainingSigns : Fin VV := ⟨103,by decide⟩

/-- `sec:walks` and `lem:print`, paper/paper.tex: remove one actual low sign bit by exact binary division. -/
def readNextSign : St VV MM :=
  .seq (.op (.dm remainingSigns v2 tupleQuotient selectedTokenBit))
    (.op (.copy remainingSigns tupleQuotient))

/-- `sec:walks`, `lem:print` and `prop:time`, paper/paper.tex: the next edge sign is
physically obtained from the supplied original ordinal, with all retained
source records and coefficient caches unchanged. -/
theorem readNextSign_run (C : Ctx) (code index : ℕ)
    (a : DS VV MM) (hc : Cst a) (hs : a.env remainingSigns=code/2^index)
    (hfour : 4≤2^C.Wd) :
    Hs C readNextSign a 3 (fun z=>
      z.env remainingSigns=code/2^(index+1) ∧
      z.env selectedTokenBit=(code.testBit index).toNat ∧
      z.sh=a.sh ∧ Cst z ∧ Fr a z [remainingSigns,tupleQuotient,selectedTokenBit]) := by
  have hbit : code/2^index%2=(code.testBit index).toNat := by
    rw [Nat.testBit_eq_decide_div_mod_eq]
    rcases Nat.mod_two_eq_zero_or_one (code/2^index) with h | h <;> simp [h]
  unfold readNextSign
  refine Hs.seq (t1 := 1) (t2 := 1)
    (hs_dm C remainingSigns v2 tupleQuotient selectedTokenBit a
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by rw [hc.two]; omega) (by rw [hc.two]; exact hfour)) ?_
  rintro b rfl
  refine (hs_copy C remainingSigns tupleQuotient _ (by decide)).mono le_rfl ?_
  rintro z rfl
  refine ⟨?_,?_,rfl,?_,
    (Fr.set _ _ (by simp)).trans ((Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp)))⟩
  · change a.env remainingSigns/a.env v2=code/2^(index+1)
    rw [hs,hc.two,Nat.div_div_eq_div_mul,pow_succ]
  · change a.env remainingSigns%a.env v2=(code.testBit index).toNat
    rw [hs,hc.two,hbit]
  · exact Cst.of_fr (T := [remainingSigns,tupleQuotient,selectedTokenBit]) hc
      ((Fr.set _ _ (by simp)).trans ((Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp)))) (by decide)

end NearQuarticWires.StageCert.Tokens
