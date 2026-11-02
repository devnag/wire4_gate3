import Proof.Quartic.StageGamma.LabelPrepare
import Proof.Wire_3_5.SeedFixSampObjective

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageGamma

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open NearCubicWires.WireExponent3_5

/-- `cor:conditional`, paper/paper.tex: the actual
side length is formed once from the ORIGINAL side exponent. -/
def gammaSide : Fin VV := ⟨58, by decide⟩

/-- `cor:conditional`, paper/paper.tex: the ORIGINAL
eight vertices remain in their parser-assigned binary variables. -/
def gammaVertex (slot : Fin 8) : Fin VV :=
  ⟨26 + slot.val, by change 26 + slot.val < 128; omega⟩

/-- `cor:conditional`, paper/paper.tex: the row
slot of an alternating closed-walk edge, including the final wrap. -/
def gammaRowSlot (slot : Fin 8) : Fin 8 :=
  if slot.val % 2 = 0 then slot else Shared.nextSlot (by decide) slot

/-- `cor:conditional`, paper/paper.tex: the column
slot of an alternating closed-walk edge, including the final wrap. -/
def gammaColumnSlot (slot : Fin 8) : Fin 8 :=
  if slot.val % 2 = 0 then Shared.nextSlot (by decide) slot else slot

/-- `cor:conditional`, paper/paper.tex: a cell is
physically packed as column + N·row, exactly as in the Gaussian codec. -/
def prepareCell (slot : Fin 8) : St VV MM :=
  .seq (.op (.mul gammaSide (gammaVertex (gammaRowSlot slot)) (gammaCell slot)))
    (.op (.add (gammaCell slot) (gammaVertex (gammaColumnSlot slot))))

/-- `cor:conditional`, paper/paper.tex: the fixed
row and column variables name exactly the ORIGINAL walk edge. -/
theorem gammaEdge_slots (request : Machine.GammaRequest) (slot : Fin 8) :
    Cycle.edge (by norm_num) request.walk slot =
      (request.walk (gammaRowSlot slot), request.walk (gammaColumnSlot slot)) := by
  unfold Cycle.edge Shared.cellOf gammaRowSlot gammaColumnSlot
  split_ifs <;> rfl

/-- `cor:conditional` and `prop:time`, paper/paper.tex: paid binary multiplication and addition compute each
ORIGINAL packed cell, with its actual projected range proving no overflow. -/
theorem prepareCell_run (C : Ctx) (request : Machine.GammaRequest) (slot : Fin 8)
    (a : DS VV MM) (hc : Cst a)
    (hwidth : 2 * request.parameters.kh ≤ C.Wd)
    (hside : a.env gammaSide = request.parameters.N)
    (hvertices : ∀ i, a.env (gammaVertex i) = (request.walk i).val) :
    Hs C (prepareCell slot) a 3 (fun b =>
      b.env (gammaCell slot) =
        Sampler.cellNum request.parameters (Cycle.edge (by norm_num) request.walk slot) ∧
      Same a b ∧ Cst b ∧ Fr a b [gammaCell slot]) := by
  have hr : gammaSide ≠ gammaVertex (gammaRowSlot slot) := by
    intro h
    have := congrArg Fin.val h
    dsimp [gammaSide, gammaVertex] at this
    have := (gammaRowSlot slot).isLt
    omega
  have hsc : gammaSide ≠ gammaCell slot := by
    intro h
    have := congrArg Fin.val h
    dsimp [gammaSide, gammaCell] at this
    omega
  have hrc : gammaVertex (gammaRowSlot slot) ≠ gammaCell slot := by
    intro h
    have := congrArg Fin.val h
    dsimp [gammaVertex, gammaCell] at this
    have := (gammaRowSlot slot).isLt
    omega
  have hcc : gammaCell slot ≠ gammaVertex (gammaColumnSlot slot) := by
    intro h
    have := congrArg Fin.val h
    dsimp [gammaVertex, gammaCell] at this
    have := (gammaColumnSlot slot).isLt
    omega
  let u := (request.walk (gammaRowSlot slot)).val
  let v := (request.walk (gammaColumnSlot slot)).val
  have huv : v + request.parameters.N * u < request.parameters.N * request.parameters.N := by
    have hu := (request.walk (gammaRowSlot slot)).isLt
    have hv := (request.walk (gammaColumnSlot slot)).isLt
    dsimp [u, v]
    nlinarith
  have hpow : request.parameters.N * request.parameters.N = 2 ^ (2 * request.parameters.kh) := by
    change 2 ^ request.parameters.kh * 2 ^ request.parameters.kh = _
    rw [two_mul, pow_add]
  have hfit : v + request.parameters.N * u < 2 ^ C.Wd :=
    huv.trans_le (hpow ▸ Nat.pow_le_pow_right (by decide) hwidth)
  have hconst : vZ ∉ [gammaCell slot] ∧ v1 ∉ [gammaCell slot] ∧ v2 ∉ [gammaCell slot] := by
    fin_cases slot <;> decide
  unfold prepareCell
  refine Hs.seq (t1 := 1) (t2 := 1)
    (hs_mul C gammaSide (gammaVertex (gammaRowSlot slot)) (gammaCell slot) a
      hr hsc hrc (by rw [hside, hvertices]; change request.parameters.N * u < _; omega)) ?_
  intro b hb
  subst hb
  let b := a.set (gammaCell slot) (a.env gammaSide * a.env (gammaVertex (gammaRowSlot slot)))
  have hbc : Cst b := Cst.of_fr hc (Fr.set a _ (by simp)) hconst
  have hbcell : b.env (gammaCell slot) = request.parameters.N * u := by
    simp [b, hside, hvertices, u]
  have hbcol : b.env (gammaVertex (gammaColumnSlot slot)) = v := by
    rw [DS.set_env_ne _ _ hcc.symm]
    exact hvertices _
  refine Hs.mono (hs_add C (gammaCell slot) (gammaVertex (gammaColumnSlot slot)) b hcc
    (by rw [hbcell, hbcol]; omega)) le_rfl ?_
  rintro d rfl
  refine ⟨?_, (Same.set a _ _).trans (Same.set b _ _),
    Cst.of_fr hbc (Fr.set b _ (by simp)) hconst,
    (Fr.set a _ (by simp)).trans (Fr.set b _ (by simp))⟩
  rw [DS.set_env_self, hbcell, hbcol, gammaEdge_slots]
  have hh := SeedFix.cellNumC_eq (P := request.parameters)
    (request.walk (gammaRowSlot slot), request.walk (gammaColumnSlot slot))
  simpa [SeedFix.cellNumC, u, v, Nat.add_comm] using hh

end NearQuarticWires.StageGamma
