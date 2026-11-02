import Proof.Gates.Dispatch.Expr

/-!
# Finite sequences of binary arithmetic assignments

Paper: `sec:algorithm`, paper/paper.tex. The endpoint
numerators are fixed arithmetic expressions in the parsed fields. A finite
sequence of assignments has the literal fold semantics below, with an
explicit sum of the compiled expression costs.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageOutput

open NearCubicGates.Close.Dispatch

abbrev Assignment := Fin VV × AE

def lowAgree (a b : Fin VV → ℕ) : Prop :=
  ∀ y, y.val < 200 → y ≠ vJ → b y = a y

theorem lowAgree_eval {a b : Fin VV → ℕ} (h : lowAgree a b) (e : AE) (he : e.vars_ok) :
    e.eval b = e.eval a :=
  eval_congr e he ⟨a, 0, 0, []⟩ ⟨b, 0, 0, []⟩ 0 h

theorem lowAgree_ok {a b : Fin VV → ℕ} (h : lowAgree a b) (W : ℕ) (e : AE) (he : e.vars_ok) :
    e.ok W b ↔ e.ok W a :=
  ok_congr W e he ⟨a, 0, 0, []⟩ ⟨b, 0, 0, []⟩ 0 h

theorem lowAgree_update {a b : Fin VV → ℕ} (h : lowAgree a b)
    (x : Fin VV) (e : AE) (he : e.vars_ok) :
    lowAgree (Function.update a x (e.eval a)) (Function.update b x (e.eval b)) := by
  intro y hy hj
  by_cases hxy : y = x
  · subst hxy; simp only [Function.update_self]; exact lowAgree_eval h e he
  · rw [Function.update_of_ne hxy, Function.update_of_ne hxy]
    exact h y hy hj

def assignmentsLegal (xs : List Assignment) : Prop :=
  ∀ p ∈ xs, p.1.val < 200 ∧ p.1 ∉ [vZ, v1, v2, vPOS] ∧ p.2.vars_ok ∧ p.2.depth + 1 < 50

def assignmentEnv : List Assignment → (Fin VV → ℕ) → (Fin VV → ℕ)
  | [], env => env
  | (x, e) :: xs, env => assignmentEnv xs (Function.update env x (e.eval env))

def assignmentsSafe (W : ℕ) : List Assignment → (Fin VV → ℕ) → Prop
  | [], _ => True
  | (x, e) :: xs, env => e.ok W env ∧ assignmentsSafe W xs (Function.update env x (e.eval env))

theorem assignmentEnv_congr (xs : List Assignment) (hl : assignmentsLegal xs)
    {a b : Fin VV → ℕ} (h : lowAgree a b) : lowAgree (assignmentEnv xs a) (assignmentEnv xs b) := by
  induction xs generalizing a b with
  | nil => exact h
  | cons p xs ih =>
    exact ih (fun q hq => hl q (List.mem_cons_of_mem _ hq))
      (lowAgree_update h p.1 p.2 (hl p (List.mem_cons_self)).2.2.1)

theorem assignmentsSafe_congr (W : ℕ) (xs : List Assignment) (hl : assignmentsLegal xs)
    {a b : Fin VV → ℕ} (h : lowAgree a b) : assignmentsSafe W xs b ↔ assignmentsSafe W xs a := by
  induction xs generalizing a b with
  | nil => rfl
  | cons p xs ih =>
    change p.2.ok W b ∧ assignmentsSafe W xs (Function.update b p.1 (p.2.eval b)) ↔ _
    rw [lowAgree_ok h W p.2 (hl p (List.mem_cons_self)).2.2.1]
    rw [ih (fun q hq => hl q (List.mem_cons_of_mem _ hq))
      (lowAgree_update h p.1 p.2 (hl p (List.mem_cons_self)).2.2.1)]
    rfl

def assignmentProgram : List Assignment → St VV
  | [] => skipS
  | (x, e) :: xs => .seq (assign x e) (assignmentProgram xs)

def assignmentCost (xs : List Assignment) : ℕ := (xs.map fun p => p.2.cost + 3).sum + 1

theorem assignmentProgram_spec {C : Ctx} (xs : List Assignment) (hl : assignmentsLegal xs) :
    ∀ a : DS VV, Cst a → assignmentsSafe C.Wd xs a.env →
    Hs C (assignmentProgram xs) a (assignmentCost xs) (fun b =>
      lowAgree (assignmentEnv xs a.env) b.env ∧ b.cp = a.cp ∧
      b.wq = a.wq ∧ b.out = a.out ∧ Cst b) := by
  induction xs with
  | nil =>
    intro a hc _
    refine Hs.mono (skip_spec a) (by simp [assignmentCost]) ?_
    rintro b rfl
    refine ⟨fun y _ hj => DS.set_env_ne a 0 hj, rfl, rfl, rfl, ?_⟩
    exact ⟨by rw [DS.set_env_ne _ _ (by decide)]; exact hc.z,
      by rw [DS.set_env_ne _ _ (by decide)]; exact hc.one,
      by rw [DS.set_env_ne _ _ (by decide)]; exact hc.two,
      by rw [DS.set_env_ne _ _ (by decide)]; exact hc.pos⟩
  | cons p xs ih =>
    intro a hc hs
    have hp := hl p (List.mem_cons_self)
    have ht : assignmentsLegal xs := fun q hq => hl q (List.mem_cons_of_mem _ hq)
    refine Hs.mono (Hs.seq (t2 := assignmentCost xs)
      (assign_spec p.1 hp.1 hp.2.1 p.2 a hp.2.2.1 hp.2.2.2 hc hs.1)
      (fun b hb => ?_)) (by simp [assignmentCost]; omega) (fun _ h => h)
    obtain ⟨bv, bf, bp, bw, bo, bc⟩ := hb
    have bagree : lowAgree (Function.update a.env p.1 (p.2.eval a.env)) b.env := by
      intro y hy hj
      by_cases hxy : y = p.1
      · subst hxy; rw [Function.update_self]; exact bv
      · rw [Function.update_of_ne hxy]
        exact bf y hy hj hxy
    have bs : assignmentsSafe C.Wd xs b.env :=
      (assignmentsSafe_congr C.Wd xs ht bagree).mpr hs.2
    refine Hs.mono (ih ht b bc bs) le_rfl ?_
    rintro d ⟨de, dp, dw, dout, dc⟩
    refine ⟨?_, by rw [dp, bp], by rw [dw, bw], by rw [dout, bo], dc⟩
    intro y hy hj
    exact (de y hy hj).trans (assignmentEnv_congr xs ht bagree y hy hj)

end NearQuarticWires.StageOutput
