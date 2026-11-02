import Proof.Quartic.StagePrep.CensusWeights

/-!
# The complete top-coefficient test

Paper: normalized `SYM` calls, paper/paper.tex,
and `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open NearCubicWires NearCubicGates.Close.Interfaces

/-- The full coefficient-list test of `sec:counting`, paper/paper.tex. -/
def checkCoefficients : St VV :=
  .loop (.lt weightIndex weightLength)
    (.seq checkUnitCoefficient (.op (.inc weightIndex)))

/-- Every coefficient of the normalized call in `sec:counting`, paper/paper.tex is tested, including its sign. -/
theorem checkCoefficients_spec (C : Ctx) (cs : List ℤ) (rest : List Bool)
    (a : DS VV) (hc : Cst a) (P0 : Prop) [Decidable P0]
    (hflag : a.env censusUnit = bnat P0)
    (hi : a.env weightIndex = 0) (hn : a.env weightLength = cs.length)
    (hcw : C.cw.drop a.cp = cs.flatMap intWord ++ rest)
    (hW : C.cw.length + 2 ≤ C.Wd) (hL : C.cw.length + 2 < 2 ^ C.Wd) :
    Hs C checkCoefficients a (cs.length * (60 * C.cw.length + 78) + 2) (fun b =>
      b.env censusUnit = bnat (P0 ∧ ∀ z ∈ cs, z = 1) ∧
      b.cp = a.cp + (cs.flatMap intWord).length ∧
      b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      Fr a b (weightIndex :: censusUnit :: readIntT) ∧
      b.env weightIndex = cs.length ∧ b.env weightLength = cs.length) := by
  let T := weightIndex :: censusUnit :: readIntT
  let P : ℕ → DS VV → Prop := fun k b =>
    b.env censusUnit = bnat (P0 ∧ ∀ z ∈ cs.take k, z = 1) ∧
    b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ Fr a b T
  have hp : ∀ k b v, P k b → P k (b.set weightIndex v) := by
    rintro k b v ⟨hb, hw, ho, hc', hfr⟩
    exact ⟨by rw [DS.set_env_ne _ _ (by decide)]; exact hb, hw, ho,
      ⟨by rw [DS.set_env_ne _ _ (by decide)]; exact hc'.z,
       by rw [DS.set_env_ne _ _ (by decide)]; exact hc'.one,
       by rw [DS.set_env_ne _ _ (by decide)]; exact hc'.two,
       by rw [DS.set_env_ne _ _ (by decide)]; exact hc'.pos⟩,
      Fr.trans hfr (Fr.set _ _ (by decide))⟩
  have hbody : ∀ k (hk : k < cs.length) (b : DS VV), P k b →
      b.env weightIndex = k → b.env weightLength = cs.length →
      C.cw.drop b.cp = intWord cs[k] ++ ((cs.drop (k + 1)).flatMap intWord ++ rest) →
      Hs C checkUnitCoefficient b (60 * C.cw.length + 74) (fun d =>
        P (k + 1) d ∧ d.env weightIndex = k ∧ d.env weightLength = cs.length ∧
        d.cp = b.cp + (intWord cs[k]).length) := by
    intro k hk b ⟨hb, hw, ho, hc', hfr⟩ hbi hbn hd
    have hentry := len_le_of_drop hd
    refine Hs.mono (checkUnitCoefficient_spec C b hc' cs[k] _ _ hb hd hW hL)
      (by omega) ?_
    rintro d ⟨hdflag, hdcp, hdwq, hdout, hdc, hdfr⟩
    refine ⟨⟨?_, hdwq.trans hw, hdout.trans ho, hdc,
      Fr.trans hfr (Fr.weaken hdfr (by decide))⟩,
      (hdfr _ (by decide)).trans hbi, (hdfr _ (by decide)).trans hbn, hdcp⟩
    rw [hdflag]
    apply bnat_congr
    rw [← take_succ_iff cs (· = 1) k hk]
    tauto
  have hcs : cs.length ≤ C.cw.length := by
    have hlist := length_le_flatMap cs intWord intWord_len_pos
    have hlen := len_le_of_drop hcw
    omega
  have hwalk := walk (C := C) cs intWord weightIndex weightLength (by decide)
    checkUnitCoefficient P (60 * C.cw.length + 74) rest hp hbody (by omega) a
    ⟨by simpa only [List.take_zero, List.not_mem_nil, false_implies,
      implies_true, and_true] using hflag, rfl, rfl, hc, Fr.refl _ _⟩ hi hn hcw
  refine Hs.mono hwalk le_rfl ?_
  rintro b ⟨⟨hb, hw, ho, hc', hfr⟩, hbi, hbn, hbcp⟩
  exact ⟨by simpa only [List.take_length] using hb, hbcp, hw, ho, hc', hfr, hbi, hbn⟩

end NearQuarticWires.StagePrep
