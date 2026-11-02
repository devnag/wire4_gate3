import Proof.Quartic.StageOutput.Layout
import Proof.Quartic.StageOutput.Marked
import Proof.Gates.Dispatch.Print

/-!
# Explicit allocation for the dyadic output

Paper: `sec:algorithm`, paper/paper.tex, and `prop:time`. Writing `n` padding bits gives the subsequent arithmetic
machine enough width to represent the denominator `2^(n+1)`. This loop
is charged for every bit it writes, even when `n` has a short binary code.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageOutput

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Dispatch

def padIndex : Fin VV := ⟨70, by decide⟩
def inputN : Fin VV := ⟨20, by decide⟩

def appendPadding : St VV :=
  .seq (.op (.zero padIndex))
    (.loop (.lt padIndex inputN) (.seq (.op (.emit false)) (.op (.inc padIndex))))

theorem appendPadding_spec {C : Ctx} (a : DS VV) (hc : Cst a)
    (hn : a.env inputN < 2 ^ C.Wd) :
    Hs C appendPadding a (5 * a.env inputN + 4) (fun b =>
      b.out = a.out ++ List.replicate (a.env inputN) false ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ Cst b ∧ Fr a b [padIndex]) := by
  let I : ℕ → DS VV → Prop := fun k b =>
    b.env padIndex = k ∧ b.env inputN = a.env inputN ∧
    b.out = a.out ++ List.replicate k false ∧ b.cp = a.cp ∧ b.wq = a.wq ∧ Fr a b [padIndex]
  have hl := Hs.loopN (C := C) (c := .lt padIndex inputN)
    (s := .seq (.op (.emit false)) (.op (.inc padIndex))) (show padIndex ≠ inputN by decide)
    I (a.env inputN) 3 (by
      rintro k hk b ⟨hi, hn', ho, hp, hw, hf⟩
      refine ⟨by simp [Cnd.eval, hi, hn', hk], ?_⟩
      refine Hs.seq (t2 := 1) (hs_emit C false b) (fun d hd => ?_)
      subst hd
      refine Hs.mono (hs_inc C padIndex _ (by change b.env padIndex + 1 < _; rw [hi]; omega)) le_rfl ?_
      rintro e rfl
      refine ⟨by simp [hi], ?_, ?_, hp, hw, ?_⟩
      · rw [DS.set_env_ne _ _ (by decide)]
        exact hn'
      · change b.out ++ [false] = a.out ++ List.replicate (k + 1) false
        rw [ho, List.replicate_succ', List.append_assoc]
      · intro y hy
        rw [DS.set_env_ne _ _ (by simpa using hy)]
        exact hf y hy)
    (by rintro b ⟨hi, hn', _⟩; simp [Cnd.eval, hi, hn'])
  refine Hs.mono (Hs.seq (t2 := a.env inputN * (3 + 2) + 2)
    (hs_zero C padIndex a) (fun b hb => ?_)) (by omega) (fun _ h => h)
  subst hb
  refine Hs.mono (hl _ ⟨by simp, by rw [DS.set_env_ne _ _ (by decide)], by simp, rfl, rfl,
    Fr.set a 0 (by simp)⟩) le_rfl ?_
  rintro d ⟨_, _, ho, hp, hw, hf⟩
  refine ⟨ho, hp, hw, ?_, hf⟩
  exact Cst.of_fr hc hf (by decide) (by rw [hf vPOS (by decide), hp]; exact hc.pos)

end NearQuarticWires.StageOutput
