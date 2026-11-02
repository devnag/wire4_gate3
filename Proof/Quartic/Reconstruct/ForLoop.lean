import Proof.Quartic.Reconstruct.PrintHeadRun

/-!
# Counted loops that write

`forS i n body` runs `body` for `i = 0, 1, …, n - 1` (`n` held in a variable). If the `k`-th run writes `w k` and keeps
an invariant, the loop writes `(List.range N).flatMap w` (`forS_spec`). The printing stage writes its lists with it.
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearCubicGates.Close.Cells

variable {C : Ctx}

/-- Run `body` for `i = 0, …, n - 1`. -/
def forS (i n : Fin VV) (body : St VV MM) : St VV MM :=
  .seq (.op (.zero i)) (.loop (.lt i n) (.seq body (.op (.inc i))))

theorem range_succ_flatMap {α : Type} (w : ℕ → List α) (k : ℕ) :
    (List.range (k + 1)).flatMap w = (List.range k).flatMap w ++ w k := by
  rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]

/-- **A counted loop that writes.** -/
theorem forS_spec (i n : Fin VV) (hin : i ≠ n) (body : St VV MM) (N t : ℕ) (w : ℕ → List Bool)
    (Inv : ℕ → DS VV MM → Prop) (hset : ∀ k a v, Inv k a → Inv k (a.set i v))
    (hstep : ∀ k < N, ∀ a, Inv k a → a.env i = k → a.env n = N →
      Hs C body a t (fun b => Inv (k + 1) b ∧ b.env i = k ∧ b.env n = N ∧ b.out = a.out ++ w k))
    (a : DS VV MM) (h0 : Inv 0 a) (hn : a.env n = N) (hN : N < 2 ^ C.Wd) :
    Hs C (forS i n body) a (N * (t + 4) + 4)
      (fun b => Inv N b ∧ b.env n = N ∧ b.out = a.out ++ (List.range N).flatMap w) := by
  let J : ℕ → DS VV MM → Prop := fun k b => Inv k b ∧ b.env i = k ∧ b.env n = N ∧
    b.out = a.out ++ (List.range k).flatMap w
  have loop : ∀ b, J 0 b → Hs C (.loop (.lt i n) (.seq body (.op (.inc i)))) b (N * ((t + 2) + 2) + 2) (J N) := by
    refine Hs.loopN (c := .lt i n) hin J N (t + 2) ?_ ?_
    · intro k hk b ⟨h1, h2, h3, h4⟩
      refine ⟨by simp [Cnd.eval, h2, h3, hk], ?_⟩
      refine Hs.seq (t1 := t) (t2 := 1) (hstep k hk b h1 h2 h3) (fun c ⟨c1, c2, c3, c4⟩ => ?_)
      refine Hs.mono (hs_inc C i c (lt_of_le_of_lt (show c.env i + 1 ≤ N by rw [c2]; exact hk) hN)) le_rfl ?_
      rintro d rfl
      refine ⟨hset _ _ _ c1, by rw [DS.set_env_self, c2], by rw [DS.set_env_ne _ _ (Ne.symm hin), c3], ?_⟩
      rw [DS.set_out, c4, h4, range_succ_flatMap, List.append_assoc]
    · intro b ⟨_, h2, h3, _⟩
      simp [Cnd.eval, h2, h3]
  refine Hx.hs (Hs.then (hs_zero C i a) (fun b0 hb0 n0 hn0 => ?_))
  subst hb0
  refine Hs.last (loop _ ⟨hset _ _ _ h0, DS.set_env_self _ _ _, by rw [DS.set_env_ne _ _ (Ne.symm hin), hn],
    by simp⟩) (fun b ⟨b1, _, b3, b4⟩ m hm => ⟨⟨b1, b3, b4⟩, by nlinarith⟩)

end NearQuarticWires.Reconstruct
