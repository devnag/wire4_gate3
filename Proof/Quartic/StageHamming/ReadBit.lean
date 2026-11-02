import Proof.Gates.Cells.Arith

set_option autoImplicit false

namespace NearQuarticWires.StageHamming

open NearCubicGates.Close.Cells

def bitInput : Fin VV := 120
def bitIndex : Fin VV := 121
def bitOutput : Fin VV := 122
def bitWork : Fin VV := 123
def bitCounter : Fin VV := 124
def bitQuotient : Fin VV := 125

/-- `imp:partition` and `imp:pullback`, paper/paper.tex: ordinary shifts and remainder physically select one bit
of a scalar center code, without a precomputed coordinate list. -/
def readScalarBit : St VV MM :=
  .seq (.op (.copy bitWork bitInput))
    (.seq (forS bitCounter bitIndex (.op (.half bitWork)))
      (.op (.dm bitWork v2 bitQuotient bitOutput)))

/-- `imp:pullback`, paper/paper.tex: the physical scalar
reader returns the literal requested bit, preserving every other
register and every non-register machine component. -/
theorem readScalarBit_spec {C : Ctx} (a : DS VV MM) (hc : Cst a)
    (hi : a.env bitIndex < 2 ^ C.Wd) (hW : 2 ≤ C.Wd) :
    Hs C readScalarBit a (5 * a.env bitIndex + 9) (fun b =>
      b.env bitOutput = ((a.env bitInput).testBit (a.env bitIndex)).toNat ∧
      b.sh = a.sh ∧ Fr a b [bitWork, bitCounter, bitQuotient, bitOutput]) := by
  let X := a.env bitInput
  let I := a.env bitIndex
  refine Hs.mono (Hs.seq (t1 := 1) (t2 := 5 * I + 6)
    (hs_copy C bitWork bitInput a (by decide)) (fun b hb => ?_))
    (by dsimp only [I]; omega) (fun _ h => h)
  subst hb
  let Inv : ℕ → DS VV MM → Prop := fun k b =>
    b.env bitWork = X / 2 ^ k ∧ b.sh = a.sh ∧ Fr a b [bitWork, bitCounter]
  have hloop := forS_spec' (C := C) bitCounter bitIndex (by decide)
    (.op (.half bitWork)) (a.set bitWork (a.env bitInput)) I hi Inv 1
    (fun k b v hb => by
      refine ⟨?_, hb.2.1, Fr.trans hb.2.2 (Fr.set _ _ (by simp))⟩
      rw [DS.set_env_ne _ _ (by decide)]
      exact hb.1)
    (by refine ⟨?_, rfl, Fr.set _ _ (by simp)⟩; simp [X])
    (by rw [DS.set_env_ne _ _ (by decide)]) ?_
  · refine Hs.seq (t1 := 5 * I + 4) (t2 := 1)
      (hloop.mono (by omega) (fun _ h => h)) (fun b hb => ?_)
    obtain ⟨⟨hwork, hsh, hfr⟩, _, _⟩ := hb
    have hv2 : b.env v2 = 2 := by rw [hfr _ (by decide)]; exact hc.two
    refine Hs.mono (hs_dm C bitWork v2 bitQuotient bitOutput b
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by omega) (by
        rw [hv2]
        calc
          2 * 2 = (2 : ℕ) ^ 2 := by norm_num
          _ ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (by norm_num) hW)) le_rfl ?_
    rintro c rfl
    refine ⟨?_, hsh, Fr.trans (hfr.weaken (by simp))
      (Fr.trans (Fr.set _ _ (by simp)) (Fr.set _ _ (by simp)))⟩
    rw [DS.set_env_self, hwork, hv2, Nat.testBit_eq_decide_div_mod_eq]
    rcases Nat.mod_two_eq_zero_or_one (X / 2 ^ I) with hz | ho
    · simp [X, I, hz]
    · simp [X, I, ho]
  · intro k hk b hb hcount hindex
    refine Hs.mono (hs_half C bitWork b) le_rfl ?_
    rintro c rfl
    refine ⟨⟨?_, hb.2.1, Fr.trans hb.2.2 (Fr.set _ _ (by simp))⟩, ?_, ?_⟩
    · rw [DS.set_env_self, hb.1, Nat.div_div_eq_div_mul, ← pow_succ]
    · rw [DS.set_env_ne _ _ (by decide)]
      exact hcount
    · rw [DS.set_env_ne _ _ (by decide)]
      exact hindex

end NearQuarticWires.StageHamming
