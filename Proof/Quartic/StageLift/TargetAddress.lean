import Proof.Quartic.StageLift.DegreeProgram
import Proof.Quartic.StageLift.IndexLookup

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicGates.Close.Cells

/-- `lem:residue`, paper/paper.tex: actual
target-bank addressing uses the current circuit and chain row. -/
def targetCircuit : Fin VV := 126
def targetRow : Fin VV := 124
def targetAddress : Fin VV := 67
def targetHeaderSize : Fin VV := 69

/-- `lem:residue` and Step 3, paper/paper.tex: digit records follow the ten literal header records,
in the original circuit-major order. -/
def digitTargetAddress : St VV MM :=
  .seq (.op (.mul targetCircuit degreeChain targetAddress))
    (.seq (.op (.add targetAddress targetRow))
      (.seq (setK targetHeaderSize 10) (.op (.add targetAddress targetHeaderSize))))

/-- `lem:residue` and Step 3, paper/paper.tex: the two score targets follow both complete digit banks. -/
def scoreTargetAddress : St VV MM :=
  .seq (.op (.copy targetAddress degreeChain))
    (.seq (.op (.shl targetAddress))
      (.seq (.op (.add targetAddress targetCircuit))
        (.seq (setK targetHeaderSize 10) (.op (.add targetAddress targetHeaderSize)))))

/-- `lem:residue` and Step 3, paper/paper.tex: no target address is inferred from a logical row;
the address is computed from the actual three loaded loop fields. -/
theorem digitTargetAddress_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (J row : ℕ) (circuit : Fin 2) (hrow : row < J)
    (hJ : a.env degreeChain = J) (hr : a.env targetRow = row)
    (hj : a.env targetCircuit = circuit.val) (hfit : 2 * J + 11 < 2 ^ C.Wd) :
    Hs C digitTargetAddress a 40 (fun b =>
      b.env targetAddress = 10 + circuit.val * J + row ∧ b.sh = a.sh ∧
      Cst b ∧ Fr a b [targetAddress, targetHeaderSize, vJ]) := by
  unfold digitTargetAddress
  apply Hx.hs
  refine Hs.then (hs_mul C targetCircuit degreeChain targetAddress a
    (by decide) (by decide) (by decide) (by rw [hj, hJ]; nlinarith [circuit.isLt]))
    (fun b hb n1 hn1 => ?_)
  subst b
  let s1 := a.set targetAddress (a.env targetCircuit * a.env degreeChain)
  refine Hs.then (hs_add C targetAddress targetRow s1 (by decide)
    (by dsimp [s1]; vsimp [hj, hJ, hr]; nlinarith [circuit.isLt]))
    (fun b hb n2 hn2 => ?_)
  subst b
  let s2 := s1.set targetAddress (s1.env targetAddress + s1.env targetRow)
  refine Hs.then (setK_spec targetHeaderSize (by decide) 10 s2 (by omega))
    (fun b ⟨h10, hbsh, hbfr⟩ n3 hn3 => ?_)
  have haddr : b.env targetAddress = circuit.val * J + row := by
    rw [hbfr _ (by decide)]
    dsimp [s2, s1]
    vsimp [hj, hJ, hr]
  refine Hs.last (hs_add C targetAddress targetHeaderSize b (by decide)
    (by rw [haddr, h10]; nlinarith [circuit.isLt]))
    (fun z hz n4 hn4 => ?_)
  subst z
  have hf : Fr a (b.set targetAddress (b.env targetAddress + b.env targetHeaderSize))
      [targetAddress, targetHeaderSize, vJ] :=
    (Fr.set a _ (by simp)).trans ((Fr.set s1 _ (by simp)).trans
      ((hbfr.weaken (by simp)).trans (Fr.set b _ (by simp))))
  refine ⟨⟨?_, hbsh, Cst.of_fr hc hf (by decide), hf⟩, by omega⟩
  simp only [DS.set_env_self, haddr, h10]
  omega

/-- `lem:residue` and Step 3, paper/paper.tex: score addressing skips the physically retained two
digit banks and uses the actual circuit ordinal. -/
theorem scoreTargetAddress_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (J : ℕ) (circuit : Fin 2) (hJ : a.env degreeChain = J)
    (hj : a.env targetCircuit = circuit.val) (hfit : 2 * J + 11 < 2 ^ C.Wd) :
    Hs C scoreTargetAddress a 40 (fun b =>
      b.env targetAddress = 10 + 2 * J + circuit.val ∧ b.sh = a.sh ∧
      Cst b ∧ Fr a b [targetAddress, targetHeaderSize, vJ]) := by
  unfold scoreTargetAddress
  apply Hx.hs
  refine Hs.then (hs_copy C targetAddress degreeChain a (by decide))
    (fun b hb n1 hn1 => ?_)
  subst b
  let s1 := a.set targetAddress (a.env degreeChain)
  refine Hs.then (hs_shl C targetAddress s1 (by dsimp [s1]; vsimp [hJ]; omega))
    (fun b hb n2 hn2 => ?_)
  subst b
  let s2 := s1.set targetAddress (2 * s1.env targetAddress)
  refine Hs.then (hs_add C targetAddress targetCircuit s2 (by decide)
    (by dsimp [s2, s1]; vsimp [hJ, hj]; omega))
    (fun b hb n3 hn3 => ?_)
  subst b
  let s3 := s2.set targetAddress (s2.env targetAddress + s2.env targetCircuit)
  refine Hs.then (setK_spec targetHeaderSize (by decide) 10 s3 (by omega))
    (fun b ⟨h10, hbsh, hbfr⟩ n4 hn4 => ?_)
  have haddr : b.env targetAddress = 2 * J + circuit.val := by
    rw [hbfr _ (by decide)]
    dsimp [s3, s2, s1]
    vsimp [hJ, hj]
  refine Hs.last (hs_add C targetAddress targetHeaderSize b (by decide)
    (by rw [haddr, h10]; omega))
    (fun z hz n5 hn5 => ?_)
  subst z
  have hf : Fr a (b.set targetAddress (b.env targetAddress + b.env targetHeaderSize))
      [targetAddress, targetHeaderSize, vJ] :=
    (Fr.set a _ (by simp)).trans ((Fr.set s1 _ (by simp)).trans
      ((Fr.set s2 _ (by simp)).trans ((hbfr.weaken (by simp)).trans (Fr.set b _ (by simp)))))
  refine ⟨⟨?_, hbsh, Cst.of_fr hc hf (by decide), hf⟩, by omega⟩
  simp only [DS.set_env_self, haddr, h10]
  omega

end NearQuarticWires.StageLift
