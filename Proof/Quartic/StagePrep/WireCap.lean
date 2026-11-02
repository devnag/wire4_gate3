import Proof.Quartic.StagePrep.IntegerCensus
import Proof.Gates.Dispatch.Admit

/-!
# The actual wire-cap test

Paper: normalized calls, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch

/-- The physical wire-cap comparison in `sec:counting`, paper/paper.tex uses the nonzero-weight census. -/
def testWireCap : St VV :=
  .seq (.op (.copy t3 vN)) (.seq (powK 4)
    (.seq (.op (.shl t5)) (needLe censusTotal t5)))

/-- The comparison in `sec:counting`, paper/paper.tex conjoins the
prior admission flag with the actual wire cap. -/
theorem testWireCap_spec (C : Ctx) (a : DS VV) (hc : Cst a)
    (P : Prop) [Decidable P] (hP : a.env vADM = bnat P)
    (hW1 : ∀ j ≤ 4, a.env vN ^ j < 2 ^ C.Wd)
    (hW2 : 2 * a.env vN ^ 4 < 2 ^ C.Wd) :
    Hs C testWireCap a 24 (fun b =>
      b.env vADM = bnat (P ∧ a.env censusTotal ≤ 2 * a.env vN ^ 4) ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧
      Cst b ∧ Fr a b admT') := by
  unfold testWireCap
  refine Hx.hs (Hs.then (hs_copy C t3 vN a (by decide))
    (fun b0 hb0 n0 hn0 => ?_))
  subst hb0
  have hbc : Cst (a.set t3 (a.env vN)) :=
    Cst.of_fr (T := [t3]) hc (Fr.set _ _ (by simp)) (by decide)
      (by rw [DS.set_env_ne _ _ (by decide)]; exact hc.pos)
  refine Hs.then (powK_spec _ hbc 4 (by intro j hj; simp only [DS.set_env_self]; exact hW1 j hj))
    (fun b ⟨hbt, _, hbcp, hbwq, hbout, hbc', hbfr⟩ n1 hn1 => ?_)
  simp only [DS.set_env_self] at hbt
  refine Hs.then (hs_shl C t5 b (by rw [hbt]; exact hW2))
    (fun d hd n2 hn2 => ?_)
  subst hd
  have hba : b.env vADM = bnat P := by
    rw [hbfr _ (by decide), DS.set_env_ne _ _ (by decide), hP]
  refine Hs.last (needLe_spec censusTotal t5 (by decide) _ P
    (by rw [DS.set_env_ne _ _ (by decide), hba])) ?_
  rintro e ⟨hef, hecp, hewq, heout, hefr⟩ n3 hn3
  have hfr : Fr a e admT' := Fr.trans (Fr.set _ _ (by decide))
    (Fr.trans (Fr.weaken hbfr (by decide))
      (Fr.trans (Fr.set _ _ (by decide)) (Fr.weaken hefr (by decide))))
  have hcp : e.cp = a.cp := hecp.trans hbcp
  refine ⟨⟨?_, hcp, hewq.trans hbwq, heout.trans hbout,
    Cst.of_fr hc hfr (by decide)
      (by rw [hfr _ (by decide), hcp]; exact hc.pos), hfr⟩, by omega⟩
  rw [hef]
  apply bnat_congr
  rw [DS.set_env_ne _ _ (by decide), DS.set_env_self, hbt,
    hbfr _ (by decide), DS.set_env_ne _ _ (by decide)]

end NearQuarticWires.StagePrep
