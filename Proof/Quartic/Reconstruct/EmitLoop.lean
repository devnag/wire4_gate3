import Proof.Quartic.Reconstruct.ItemChild

/-!
# The loop over the gathered items

Paper: Step 3 of `sec:algorithm`, paper/paper.tex.

With the number of listed systems in `eM`, `itemsLoopS` runs `itemS` once per gathered item (`itemsLoopS_spec`):
it reads `(systemList q).flatMap (gatheredItem q)` and writes the framed tags and words of all listed systems at
depth `1`.
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces (listWord bitWord)
open NearQuarticWires.Greedy NearQuarticWires.Program

variable {C : Ctx} {B1 B2 : ℕ}

/-- The item counter. -/
def eI : Fin VV := ⟨79, by decide⟩
/-- The number of items. -/
def eM : Fin VV := ⟨80, by decide⟩

/-- Write the systems of all gathered items. -/
def itemsLoopS : St VV MM := .seq (.op (.zero eI)) (.loop (.lt eI eM) (.seq itemS (.op (.inc eI))))

/-- The variables written by `itemsLoopS`. -/
def itemsT : List (Fin VV) := eI :: itemT

/-- The word written for one listed system. -/
noncomputable def systemOut (q : ChildRequest B1 B2) (x : SystemIndex q) : List Bool :=
  RepairOrdinary.frame (systemTag q x) ++
    RepairOrdinary.frame (NearCubicGates.Close.Interfaces.Formats.sysWord (systemAt q x))

theorem StMoved.set {a b : DS VV MM} {k : ℕ} {w : List Bool} {T : List (Fin VV)} (h : StMoved a b k w T)
    {x : Fin VV} (v : ℕ) (hx : x ∈ T) : StMoved a (b.set x v) k w T :=
  ⟨h.ip, h.out, h.ram, h.rc, h.kin, h.kout, h.kc, Fr.trans h.fr (Fr.set b v hx)⟩

theorem marksD_flatMap {α : Type} (d : ℕ) (L : List α) (f : α → List Bool) :
    marksD d (L.flatMap f) = L.flatMap (fun x => marksD d (f x)) := by
  unfold marksD
  rw [List.flatMap_assoc]

/-- **All gathered items.** -/
theorem itemsLoopS_spec (q : ChildRequest B1 B2) (a : DS VV MM) (hc : Cst a) (rest : List Bool)
    (hin : C.inp.drop a.ip = (systemList q).flatMap (gatheredItem q) ++ rest) (h : CtxHeld q a)
    (hm : a.env eM = (systemList q).length) (hmW : (systemList q).length < 2 ^ C.Wd) (hW : emitWidth q ≤ C.Wd) :
    Hs C itemsLoopS a ((systemList q).length * (itemCostQ q C.Wd + 4) + 4)
      (fun b => StMoved a b ((systemList q).flatMap (gatheredItem q)).length
          (marksD 1 ((systemList q).flatMap (systemOut q))) itemsT ∧ CtxHeld q b ∧ Cst b) := by
  obtain ⟨m, hmL⟩ : ∃ m, (systemList q).length = m := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t, itemCostQ q C.Wd + 1 + 1 = t := ⟨_, rfl⟩
  let I : ℕ → DS VV MM → Prop := fun k b => b.env eI = k ∧ b.env eM = m ∧
    StMoved a b (((systemList q).take k).flatMap (gatheredItem q)).length
      (marksD 1 (((systemList q).take k).flatMap (systemOut q))) itemsT ∧ CtxHeld q b ∧ Cst b
  have hItem : ∀ y ∈ itemT, y ∈ itemsT := fun y hy => List.mem_cons_of_mem _ hy
  have loop : ∀ b, I 0 b → Hs C (.loop (.lt eI eM) (.seq itemS (.op (.inc eI)))) b (m * (t + 2) + 2) (I m) := by
    refine Hs.loopN (c := .lt eI eM) (show eI ≠ eM by decide) I m t ?_ ?_
    · intro k hk b ⟨h1, h2, h3, h4, h5⟩
      refine ⟨by simp only [Cnd.eval, h1, h2, decide_eq_true_eq]; exact hk, ?_⟩
      have hk' : k < (systemList q).length := by omega
      have e1 : (systemList q).flatMap (gatheredItem q) ++ rest = ((systemList q).take k).flatMap (gatheredItem q) ++
          (((systemList q).drop k).flatMap (gatheredItem q) ++ rest) := by
        rw [← List.append_assoc, ← List.flatMap_append, List.take_append_drop]
      have hinb : C.inp.drop b.ip = gatheredItem q (systemList q)[k] ++
          (((systemList q).drop (k + 1)).flatMap (gatheredItem q) ++ rest) := by
        rw [h3.ip, ← List.drop_drop, hin, e1, List.drop_left, List.drop_eq_getElem_cons hk', List.flatMap_cons,
          List.append_assoc]
      rw [← ht]
      refine Hs.seq (itemS_child q (systemList q)[k] (List.getElem_mem hk') b h5 _ hinb h4 hW)
        (fun e ⟨m1, c1, d1⟩ => ?_)
      have eK : e.env eI = k := by rw [m1.fr eI (by decide), h1]
      have eN : e.env eM = m := by rw [m1.fr eM (by decide), h2]
      refine Hs.mono (hs_inc C eI e (by rw [eK]; omega)) le_rfl ?_
      rintro f rfl
      refine ⟨by vsimp [eK], by vsimp [eN], ?_, c1.of_fr (fun y hy => DS.set_env_ne _ _
        (by rintro rfl; exact absurd hy (by decide))) rfl c1.rcF c1.rcDp c1.rcDn,
        ⟨by vsimp [d1.z], by vsimp [d1.one], by vsimp [d1.two]⟩⟩
      have hm := (h3.trans (m1.weaken hItem)).set (e.env eI + 1) (List.mem_cons_self)
      rw [List.take_succ_eq_append_getElem hk', List.flatMap_append, List.flatMap_singleton, List.length_append,
        List.flatMap_append, List.flatMap_singleton, marksD_append]
      exact hm
    · intro b ⟨h1, h2, _⟩
      simp [Cnd.eval, h1, h2]
  refine Hx.hs (Hs.then (hs_zero C eI a) (fun b0 hb0 n0 hn0 => ?_))
  subst hb0
  refine Hs.last (loop _ ⟨DS.set_env_self _ _ _, by vsimp [hm, hmL], ?_, h.of_fr (fun y hy => DS.set_env_ne _ _
    (by rintro rfl; exact absurd hy (by decide))) rfl h.rcF h.rcDp h.rcDn,
    ⟨by vsimp [hc.z], by vsimp [hc.one], by vsimp [hc.two]⟩⟩) (fun b ⟨_, _, h3, h4, h5⟩ n hn => ⟨?_, ?_⟩)
  · simpa [marksD_nil] using (StMoved.of_moved (Moved.refl a itemsT)).set 0 (List.mem_cons_self)
  · rw [← hmL, List.take_length] at h3
    exact ⟨h3, h4, h5⟩
  · subst ht hmL
    have : (systemList q).length * (itemCostQ q C.Wd + 1 + 1 + 2) = (systemList q).length * (itemCostQ q C.Wd + 4) := by
      ring
    omega

end NearQuarticWires.Reconstruct
