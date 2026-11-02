import Proof.Quartic.Reconstruct.EmitLoop

/-!
# Reading the context of the gathered word

Paper: Step 3 of `sec:algorithm`, paper/paper.tex.

The gathered word starts with the context of the child (`Phases.contextWord`) and the number of listed systems.
`headS` reads them (`headS_spec`): `n`, then `M_1`, `A`, `Λ`, `J` into `kM`, `kA`, `kL`, `kJ`, the rates into the
store `sF`, whether the call has two circuits and `2mG_1`, `2mG_2` into `kPair`, `kB0`, `kB1`, and the number of
systems into `eM`; the other fields are read past. It writes `frame (natWord n)` and `natWord m` at depth `1`, the
start of `frame systemsWord`.
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces (listWord bitWord)

variable {C : Ctx}

/-- Read a number into `x`. -/
def rdTo (x : Fin VV) : St VV MM := .seq rdNatI (.op (.copy x t3))

/-- Read numbers into a list of variables. -/
def rdVars : List (Fin VV) → St VV MM
  | [] => skipS
  | x :: xs => .seq (rdTo x) (rdVars xs)

theorem drop_step {inp u w : List Bool} {i : ℕ} (h : inp.drop i = u ++ w) : inp.drop (i + u.length) = w := by
  rw [← List.drop_drop, h, List.drop_left]

/-- **Reading a number into a variable.** -/
theorem rdTo_spec (x : Fin VV) (hx0 : x ∉ rdNatT ∧ x ≠ vZ ∧ x ≠ v1 ∧ x ≠ v2) (a : DS VV MM) (hc : Cst a) (v : ℕ)
    (rest : List Bool) (hin : C.inp.drop a.ip = natWord v ++ rest) (hW : natBitLength v + 2 ≤ C.Wd) :
    Hs C (rdTo x) a (30 * natBitLength v + 32)
      (fun b => b.env x = v ∧ Moved a b (natWord v).length [] (x :: rdNatT) ∧ Cst b) := by
  refine Hx.hs (Hs.then (rdNatI_spec a hc v _ hin hW) (fun b0 ⟨r1, _, r3, r4, r5⟩ n0 hn0 => ?_))
  simp only [Prod.mk.injEq] at r4
  obtain ⟨o0, m0, q0, i0, k0, kc0⟩ := r4
  have hxt : x ≠ t3 := fun h => hx0.1 (by rw [h]; decide)
  refine Hs.last (hs_copy C x t3 b0 hxt) (fun b1 hb1 n1 hn1 => ?_)
  subst hb1
  refine ⟨⟨by rw [DS.set_env_self, r1], ⟨by rw [DS.set_ip, r3], by rw [DS.set_out, o0, List.append_nil],
    by rw [DS.set_ram, m0], by rw [DS.set_rc, q0], by rw [DS.set_kin, i0], by rw [DS.set_kout, k0],
    by rw [DS.set_kc, kc0], Fr.trans (r5.weaken (fun y hy => List.mem_cons_of_mem _ hy))
      (Fr.set b0 _ List.mem_cons_self)⟩, Cst.of_fr (Cst.of_fr hc r5 (by decide)) (Fr.set b0 _ (List.mem_singleton_self x))
    (by simp only [List.mem_singleton]; exact ⟨fun h => hx0.2.1 h.symm, fun h => hx0.2.2.1 h.symm,
      fun h => hx0.2.2.2 h.symm⟩)⟩, by omega⟩

/-- **Reading numbers into variables.** -/
theorem rdVars_spec (xs : List (Fin VV)) (hnd : xs.Nodup)
    (hx : ∀ x ∈ xs, x ∉ rdNatT ∧ x ≠ vZ ∧ x ≠ v1 ∧ x ≠ v2) (vs : List ℕ) (hl : vs.length = xs.length)
    (a : DS VV MM) (hc : Cst a) (rest : List Bool) (hin : C.inp.drop a.ip = vs.flatMap natWord ++ rest) (ℓ : ℕ)
    (hW : ∀ v ∈ vs, natBitLength v ≤ ℓ) (hℓ : ℓ + 2 ≤ C.Wd) :
    Hs C (rdVars xs) a (xs.length * (30 * ℓ + 33) + 1)
      (fun b => (∀ p ∈ xs.zip vs, b.env p.1 = p.2) ∧ Moved a b (vs.flatMap natWord).length [] (xs ++ rdNatT) ∧
        Cst b) := by
  induction xs generalizing vs a with
  | nil =>
    have hv : vs = [] := List.length_eq_zero_iff.mp (by simpa using hl)
    subst hv
    refine Hs.mono (skip_spec a) (by simp) ?_
    rintro b rfl
    exact ⟨by simp, by simpa using (Moved.refl a rdNatT).set 0 (by decide),
      ⟨by vsimp [hc.z], by vsimp [hc.one], by vsimp [hc.two]⟩⟩
  | cons x xs ih =>
    obtain ⟨v, vs, rfl⟩ : ∃ v vs', vs = v :: vs' := by
      cases vs with
      | nil => simp at hl
      | cons v vs' => exact ⟨v, vs', rfl⟩
    have hx0 := hx x (by simp)
    have hv : natBitLength v ≤ ℓ := hW v (by simp)
    have hin1 : C.inp.drop a.ip = natWord v ++ (vs.flatMap natWord ++ rest) := by
      rw [hin, List.flatMap_cons, List.append_assoc]
    refine Hx.hs (Hs.then (rdTo_spec x hx0 a hc v _ hin1 (by omega)) (fun b1 ⟨r1, m1, c1⟩ n1 hn1 => ?_))
    have hin2 : C.inp.drop b1.ip = vs.flatMap natWord ++ rest := by
      rw [m1.ip]; exact drop_step hin1
    have hnd' := (List.nodup_cons.mp hnd)
    refine Hs.last (ih hnd'.2 (fun y hy => hx y (List.mem_cons_of_mem _ hy)) vs (by simpa using hl) _ c1 hin2
      (fun w hw => hW w (List.mem_cons_of_mem _ hw))) (fun b ⟨e1, e2, e3⟩ n hn => ⟨⟨?_, ?_, e3⟩, ?_⟩)
    · intro p hp
      rw [List.zip_cons_cons, List.mem_cons] at hp
      rcases hp with rfl | hp
      · show b.env x = v
        rw [e2.fr x (by simp only [List.mem_append, not_or]; exact ⟨hnd'.1, hx0.1⟩), r1]
      · exact e1 p hp
    · have := (m1.weaken (T' := x :: (xs ++ rdNatT)) (fun y hy => by
        rcases List.mem_cons.mp hy with h | h
        · exact List.mem_cons.mpr (Or.inl h)
        · exact List.mem_cons_of_mem _ (List.mem_append_right _ h))).trans
        (e2.weaken (T' := x :: (xs ++ rdNatT)) (fun y hy => List.mem_cons_of_mem _ hy))
      simpa [List.flatMap_cons] using this
    · simp only [List.length_cons]
      have := Nat.mul_le_mul_left 30 hv
      nlinarith

end NearQuarticWires.Reconstruct
