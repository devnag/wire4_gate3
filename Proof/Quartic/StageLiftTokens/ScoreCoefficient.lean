import Proof.Quartic.StageCert.DigitOccurrence

/-!
# One occurrence of the original residue score

`lem:residue` and `lem:print`, paper/paper.tex: the Y score uses weight one on its actual circuit bank
and zero outside that bank. The program emits all eight signed edge
contributions with the original seventeen-role occurrence addresses.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageLiftTokens

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Tabulator StageCert.Tokens

def scoreCoefficient : St VV MM :=
  .seq (.op (.copy linearPositive v1))
    (.seq (.op (.zero linearNegative)) zeroOutsideCircuit)

theorem scoreCoefficient_run (C : Ctx) (circuit firstCount g : ℕ)
    (a : DS VV MM) (hc : Cst a) (hj : a.env selectedCircuit = circuit)
    (hf : a.env firstGateCount = firstCount) (hg : a.env atomOccurrence = g) :
    Hs C scoreCoefficient a 9 (fun b =>
      b.env linearPositive = selectedSummand circuit firstCount g 1 ∧
      b.env linearNegative = 0 ∧ b.sh = a.sh ∧ Cst b ∧
      Fr a b [linearPositive, linearNegative, vJ]) := by
  unfold scoreCoefficient
  refine Hs.seq (t1 := 1) (t2 := 7) (hs_copy C linearPositive v1 a (by decide)) ?_
  rintro b rfl
  let b := a.set linearPositive (a.env v1)
  refine Hs.seq (t1 := 1) (t2 := 5) (hs_zero C linearNegative b) ?_
  rintro d rfl
  let d := b.set linearNegative 0
  have hdfr : Fr a d [linearPositive, linearNegative] :=
    (Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp))
  have hdc : Cst d := Cst.of_fr hc hdfr (by decide)
  have hdp : d.env linearPositive = 1 := by dsimp [d, b]; vsimp [hc.one]
  have hdn : d.env linearNegative = 0 := rfl
  refine (zeroOutsideCircuit_run C circuit firstCount g 1 0 d hdc
    ((hdfr _ (by decide)).trans hj) ((hdfr _ (by decide)).trans hf)
    ((hdfr _ (by decide)).trans hg) hdp hdn).mono le_rfl ?_
  rintro z ⟨hzp, hzn, hzs, hzc, hzf⟩
  refine ⟨hzp, ?_, hzs, hzc, (hdfr.weaken (by simp)).trans hzf⟩
  simpa only [ite_self] using hzn

end NearQuarticWires.StageLiftTokens
