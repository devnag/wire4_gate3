import Proof.Wire_3_5.PrimTC4GeoV
import Proof.Quartic.StageHamming.ReadBit

set_option autoImplicit false

namespace NearQuarticWires.StageHamming

open NearCubicGates.Close.Cells

def paritySuccessor : Fin VV := 105
def parityWidth : Fin VV := 106
def parityPower : Fin VV := 107
def parityCounter : Fin VV := 108
def parityFlag : Fin VV := 109

/-- `imp:partition`, paper/paper.tex: the first
`k` candidate parity positions of the systematic Hamming code. -/
def parityPrefix (i k : ℕ) : Bool := (List.range k).any fun t => i + 1 == 2 ^ t

/-- `imp:partition`, paper/paper.tex: the next
canonical parity coordinate contributes exactly its power-of-two
equality to the accumulated position predicate. -/
theorem parityPrefix_succ (i k : ℕ) :
    parityPrefix i (k + 1) = (parityPrefix i k || (i + 1 == 2 ^ k)) := by
  simp [parityPrefix, List.range_succ]

/-- `imp:partition`, paper/paper.tex: one actual
power-of-two comparison records a parity position and advances
the candidate power by an ordinary shift. -/
def parityPositionStep : St VV MM :=
  .seq (.ite (.eq paritySuccessor parityPower) (.op (.copy parityFlag v1)) skipS)
    (.op (.shl parityPower))

/-- `imp:partition`, paper/paper.tex: the physical
parity-position step updates the literal prefix of the canonical code,
preserving all other scalar registers and machine components. -/
theorem parityPositionStep_spec {C : Ctx} (a : DS VV MM) (hc : Cst a)
    (i k : ℕ) (hsucc : a.env paritySuccessor = i + 1)
    (hpower : a.env parityPower = 2 ^ k)
    (hflag : a.env parityFlag = (parityPrefix i k).toNat)
    (hW : 2 ^ (k + 1) < 2 ^ C.Wd) :
    Hs C parityPositionStep a 4 (fun b =>
      b.env parityPower = 2 ^ (k + 1) ∧
      b.env parityFlag = (parityPrefix i (k + 1)).toNat ∧
      b.sh = a.sh ∧ Fr a b [parityPower, parityFlag, vJ]) := by
  have hchoose : Hs C (.ite (.eq paritySuccessor parityPower)
      (.op (.copy parityFlag v1)) skipS) a 2 (fun b =>
        b.env parityPower = 2 ^ k ∧
        b.env parityFlag = (parityPrefix i (k + 1)).toNat ∧
        b.sh = a.sh ∧ Fr a b [parityFlag, vJ]) := by
    refine Hs.ite (c := .eq paritySuccessor parityPower)
      (show paritySuccessor ≠ parityPower by decide) ?_ ?_
    · intro he
      have heq : i + 1 = 2 ^ k := by simpa only [Cnd.eval, hsucc, hpower, decide_eq_true_eq] using he
      refine Hs.mono (hs_copy C parityFlag v1 a (by decide)) le_rfl ?_
      rintro b rfl
      refine ⟨?_, ?_, rfl, Fr.set _ _ (by simp)⟩
      · rw [DS.set_env_ne _ _ (by decide), hpower]
      · rw [DS.set_env_self, hc.one, parityPrefix_succ]
        simp [heq]
    · intro he
      have hne : i + 1 ≠ 2 ^ k := by simpa only [Cnd.eval, hsucc, hpower, decide_eq_false_iff_not] using he
      refine Hs.mono (skip_spec a) le_rfl ?_
      rintro b rfl
      refine ⟨?_, ?_, rfl, Fr.set _ _ (by simp)⟩
      · rw [DS.set_env_ne _ _ (by decide), hpower]
      · rw [DS.set_env_ne _ _ (by decide)]
        simpa only [parityPrefix_succ, show (i + 1 == 2 ^ k) = false by simp [hne],
          Bool.or_false] using hflag
  refine Hs.seq (t1 := 2) (t2 := 1) hchoose (fun b hb => ?_)
  obtain ⟨hp, hf, hsh, hfr⟩ := hb
  refine Hs.mono (hs_shl C parityPower b (by rw [hp, ← pow_succ']; exact hW)) le_rfl ?_
  rintro c rfl
  refine ⟨?_, ?_, hsh, Fr.trans (hfr.weaken (by simp)) (Fr.set _ _ (by simp))⟩
  · rw [DS.set_env_self, hp, ← pow_succ']
  · rw [DS.set_env_ne _ _ (by decide)]
    exact hf

end NearQuarticWires.StageHamming
