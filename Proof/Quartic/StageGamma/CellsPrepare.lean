import Proof.Quartic.StageGamma.Labels
import Proof.Quartic.StageGamma.CellPrepare

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageGamma

open NearCubicGates.Close.Cells

/-- `cor:conditional`, paper/paper.tex: all eight
ORIGINAL packed cells are obtained by one fixed finite program. -/
def prepareCellsList : List (Fin 8) → St VV MM
  | [] => skipS
  | slot :: slots => .seq (prepareCell slot) (prepareCellsList slots)

/-- `cor:conditional`, paper/paper.tex: distinct
walk slots have distinct packed-cell destination variables. -/
theorem gammaCell_injective : Function.Injective gammaCell := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  dsimp [gammaCell] at this
  omega

/-- `cor:conditional` and `prop:time`, paper/paper.tex: exact original walk-cell packing uses real binary arithmetic
for every slot and preserves the complete request and cached field. -/
theorem prepareCellsList_run (C : Ctx) (request : Machine.GammaRequest)
    (slots : List (Fin 8)) (hn : slots.Nodup) (a : DS VV MM) (hc : Cst a)
    (hwidth : 2 * request.parameters.kh ≤ C.Wd)
    (hside : a.env gammaSide = request.parameters.N)
    (hvertices : ∀ i, a.env (gammaVertex i) = (request.walk i).val) :
    Hs C (prepareCellsList slots) a (4 * slots.length + 1) (fun b =>
      (∀ slot ∈ slots, b.env (gammaCell slot) =
        NearCubicWires.WireExponent3_5.Sampler.cellNum request.parameters
          (Cycle.edge (by norm_num) request.walk slot)) ∧
      Same a b ∧ Cst b ∧ Fr a b (slots.map gammaCell ++ [vJ])) := by
  induction slots generalizing a with
  | nil =>
    refine Hs.mono (skip_spec a) le_rfl ?_
    rintro b rfl
    exact ⟨by simp, Same.set _ _ _,
      Cst.of_fr (T := [vJ]) hc (Fr.set a 0 (by simp)) (by decide),
      Fr.set a _ (by simp)⟩
  | cons slot slots ih =>
    have hnd : slot ∉ slots ∧ slots.Nodup := by simpa using hn
    refine Hs.mono (Hs.seq (t1 := 3) (t2 := 4 * slots.length + 1)
      (prepareCell_run C request slot a hc hwidth hside hvertices) ?_)
      (by simp; omega) (fun _ h => h)
    intro b ⟨hb, hs, hbc, hfr⟩
    have hbs : b.env gammaSide = request.parameters.N := by
      rw [hfr gammaSide (by fin_cases slot <;> decide)]
      exact hside
    have hbv : ∀ i, b.env (gammaVertex i) = (request.walk i).val := by
      intro i
      rw [hfr (gammaVertex i) (by fin_cases i <;> fin_cases slot <;> decide)]
      exact hvertices i
    refine Hs.mono (ih hnd.2 b hbc hbs hbv) le_rfl ?_
    intro e ⟨he, hes, hec, hef⟩
    refine ⟨?_, hs.trans hes, hec,
      (hfr.weaken (by intro y hy; simp only [List.mem_singleton] at hy; simp [hy])).trans
        (hef.weaken (by
          intro y hy
          change y ∈ gammaCell slot :: (slots.map gammaCell ++ [vJ])
          exact List.mem_cons_of_mem _ hy))⟩
    intro i hi
    rcases List.mem_cons.mp hi with hhead | hi
    · subst i
      rw [hef (gammaCell slot) (by
        simp only [List.mem_append, List.mem_map, List.mem_singleton, not_or, not_exists]
        constructor
        · intro j ⟨hj, heq⟩
          exact hnd.1 ((gammaCell_injective heq) ▸ hj)
        · fin_cases slot <;> decide), hb]
    · exact he i hi

/-- `cor:conditional`, paper/paper.tex: exact
packing of the eight original edge cells is a fixed physical program. -/
def prepareCells : St VV MM := prepareCellsList (List.finRange 8)

/-- `cor:conditional` and `prop:time`, paper/paper.tex: all ORIGINAL Gaussian right-hand sides are produced within
a fixed ordinary clock, with every input coordinate charged and preserved. -/
theorem prepareCells_run (C : Ctx) (request : Machine.GammaRequest)
    (a : DS VV MM) (hc : Cst a)
    (hwidth : 2 * request.parameters.kh ≤ C.Wd)
    (hside : a.env gammaSide = request.parameters.N)
    (hvertices : ∀ i, a.env (gammaVertex i) = (request.walk i).val) :
    Hs C prepareCells a 33 (fun b =>
      (∀ slot, b.env (gammaCell slot) =
        NearCubicWires.WireExponent3_5.Sampler.cellNum request.parameters
          (Cycle.edge (by norm_num) request.walk slot)) ∧
      Same a b ∧ Cst b ∧ Fr a b ((List.finRange 8).map gammaCell ++ [vJ])) := by
  refine Hs.mono (prepareCellsList_run C request (List.finRange 8)
    (List.nodup_finRange _) a hc hwidth hside hvertices) (by simp) ?_
  intro b ⟨hb, hs, hbc, hf⟩
  exact ⟨fun slot => hb slot (List.mem_finRange _), hs, hbc, hf⟩

end NearQuarticWires.StageGamma
