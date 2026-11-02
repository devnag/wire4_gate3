import Proof.Quartic.StagePrep.CanonicalProgram

/-!
# The executed nonempty-prime guard

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open NearCubicGates.Close.Counter
open NearCubicGates

/-- The prime-window stage of `sec:params`, paper/paper.tex, retains all exact window fields and accepts
exactly when the actual computed dyadic prime set is nonempty. -/
theorem preparationWindowsStage_spec (C : Ctx) (a : DS VV) (hc : Cst a)
    (P : ℕ) (pair : Bool) (hPv : a.env pP=P)
    (hTag : a.env vTAG=1 ↔ pair=true) (ha : a.env vADM=1)
    (hW : 2*(P+1)*(P+1)+8 < 2^C.Wd)
    (hD : 2*(ScalarWindow.window (dyadicPrimes P)*
      (ScalarWindow.window (dyadicPrimes P)*ScalarWindow.window (dyadicPrimes P)))+
      2*ScalarWindow.window (dyadicPrimes P)+8 < 2^C.Wd) :
    Hs C preparationWindowsStage a
      (primesCost P+pairCost (ScalarWindow.window (dyadicPrimes P))+13) (fun b =>
        b.env pNP=(dyadicPrimes P).card ∧ b.env pWIN=ScalarWindow.window (dyadicPrimes P) ∧
        b.env pL2=pairSide (ScalarWindow.window (dyadicPrimes P)) ∧
        b.env pLW=windowInUse pair (pairSide (ScalarWindow.window (dyadicPrimes P)))
          (ScalarWindow.window (dyadicPrimes P)) ∧ b.env pP=P ∧
        b.env vADM=bnat (dyadicPrimes P).Nonempty ∧
        b.cp=a.cp ∧ b.wq=a.wq ∧ b.out=a.out ∧ Cst b ∧
        FrS a b (prT++pairT++[pLW,vJ,vADM])) := by
  unfold preparationWindowsStage
  refine Hx.hs (Hs.then (primeWindowsProgram_spec C a hc P pair hPv hTag hW hD)
    (fun b ⟨hbN,hbD,hbL,hbW,hbP,hbcp,hbwq,hbout,hbc,hbfr⟩ n1 hn1 => ?_))
  have hbA : b.env vADM=bnat True := by
    rw [hbfr _ (by decide) (by decide),ha]
    decide
  refine Hs.last (needLe_spec v1 pNP (by decide) b True hbA) ?_
  rintro d ⟨hdA,hdcp,hdwq,hdout,hdfr⟩ n2 hn2
  refine ⟨⟨?_,?_,?_,?_,?_,?_,hdcp.trans hbcp,hdwq.trans hbwq,hdout.trans hbout,
    Cst.of_fr hbc hdfr (by decide) (by rw [hdfr vPOS (by decide),hdcp]; exact hbc.pos),
    FrS.trans (FrS.weaken hbfr (by decide)) (FrS.weaken hdfr.toS (by decide))⟩,by omega⟩
  · exact (hdfr _ (by decide)).trans hbN
  · exact (hdfr _ (by decide)).trans hbD
  · exact (hdfr _ (by decide)).trans hbL
  · exact (hdfr _ (by decide)).trans hbW
  · exact (hdfr _ (by decide)).trans hbP
  · rw [hdA,hbc.one,hbN]
    apply bnat_congr
    simp only [true_and]
    exact Finset.one_le_card

end NearQuarticWires.StagePrep
