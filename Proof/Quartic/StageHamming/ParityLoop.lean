import Proof.Quartic.StageHamming.ParityPosition

set_option autoImplicit false

namespace NearQuarticWires.StageHamming

open NearCubicGates.Close.Cells

/-- `imp:partition`, paper/paper.tex: the actual
bounded scan of all Hamming parity positions. -/
def parityPositionLoop : St VV MM :=
  forS parityCounter parityWidth parityPositionStep

/-- `imp:partition`, paper/paper.tex: the physical
power scan computes the literal canonical parity-position predicate
from its scalar parameters, preserving every other register. -/
theorem parityPositionLoop_spec {C : Ctx} (a : DS VV MM) (hc : Cst a)
    (i s : ℕ) (hsucc : a.env paritySuccessor = i + 1)
    (hwidth : a.env parityWidth = s) (hpower : a.env parityPower = 1)
    (hflag : a.env parityFlag = 0)
    (hs : s < 2 ^ C.Wd) (hW : 2 ^ s < 2 ^ C.Wd) :
    Hs C parityPositionLoop a (8 * s + 4) (fun b =>
      b.env parityPower = 2 ^ s ∧ b.env parityFlag = (parityPrefix i s).toNat ∧
      b.sh = a.sh ∧ Fr a b [parityPower, parityFlag, vJ, parityCounter]) := by
  let Inv : ℕ → DS VV MM → Prop := fun k b =>
    b.env parityPower = 2 ^ k ∧ b.env parityFlag = (parityPrefix i k).toNat ∧
      b.env paritySuccessor = i + 1 ∧ b.sh = a.sh ∧
      Fr a b [parityPower, parityFlag, vJ, parityCounter]
  have hloop := forS_spec' (C := C) parityCounter parityWidth (by decide)
    parityPositionStep a s hs Inv 4
    (fun k b v hb => by
      refine ⟨?_, ?_, ?_, hb.2.2.2.1, Fr.trans hb.2.2.2.2 (Fr.set _ _ (by simp))⟩
      · rw [DS.set_env_ne _ _ (by decide)]; exact hb.1
      · rw [DS.set_env_ne _ _ (by decide)]; exact hb.2.1
      · rw [DS.set_env_ne _ _ (by decide)]; exact hb.2.2.1)
    (by refine ⟨?_, ?_, hsucc, rfl, Fr.refl _ _⟩
        · simpa using hpower
        · simpa [parityPrefix] using hflag)
    hwidth ?_
  · refine hloop.mono (by omega) ?_
    rintro b ⟨hb, _, _⟩
    exact ⟨hb.1, hb.2.1, hb.2.2.2.1, hb.2.2.2.2⟩
  · intro k hk b hb hcounter hswidth
    have hcB : Cst b := hc.of_fr hb.2.2.2.2 (by decide)
    have hstep := parityPositionStep_spec b hcB i k hb.2.2.1 hb.1 hb.2.1
      ((Nat.pow_le_pow_right (by norm_num) (by omega : k + 1 ≤ s)).trans_lt hW)
    refine hstep.mono le_rfl ?_
    rintro d ⟨dp, df, dsh, dfr⟩
    refine ⟨⟨dp, df, ?_, dsh.trans hb.2.2.2.1,
      Fr.trans hb.2.2.2.2 (dfr.weaken (by simp))⟩, ?_, ?_⟩
    · rw [dfr _ (by decide)]
      exact hb.2.2.1
    · rw [dfr _ (by decide)]
      exact hcounter
    · rw [dfr _ (by decide)]
      exact hswidth

end NearQuarticWires.StageHamming
