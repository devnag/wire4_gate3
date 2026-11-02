import Proof.Quartic.StageCertificateControl.CountMachine
import Proof.Quartic.StageCertTests.PrepScheduleCost

/-!
# The actual test-count bootstrap has polynomial original-source cost

Paper: Step 2 of `sec:algorithm`, paper/paper.tex,
and `prop:time`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open NearCubicGates.Close.CellsPack (Gof)
open StageCertTests (PreparedPolynomial PreparedScheduleRequest prepScheduleMass)

/-- The complete scalar-bootstrap clock in `prop:time`,
paper/paper.tex, is bounded by the actual
original-call and parameter-decoder mass, including its count codec. -/
theorem countCoreCost_le_mass (c : Call) (p : Cells.Parameters) :
    countCoreCost c p (StageCertTests.scheduleHint p)≤10^8*(prepScheduleMass c p)^4 := by
  let A := prepScheduleMass c p
  have hA : 1≤A := by dsimp [A,prepScheduleMass];omega
  have hL : (callWord c).length+1≤A := by dsimp [A,prepScheduleMass];omega
  have hJ : p.J+1≤A := by dsimp [A,prepScheduleMass];omega
  have hP : StageLift.parameterReadCost p (StageCertTests.scheduleHint p)≤A := by dsimp [A,prepScheduleMass];omega
  have hn : natBitLength c.n≤A := by dsimp [A,prepScheduleMass];omega
  have ht : natBitLength (kindTag c.kind)≤A := by dsimp [A,prepScheduleMass];omega
  have hc := StageCertTests.callCircuitCount_bounds c.kind
  have hmeta : (StageCertTests.certificateMetadata p c.kind).length≤1+256*(p.J+1) := by
    rw [StageCertTests.certificateMetadata_length]
    nlinarith [Nat.mul_le_mul_right (128*(p.J+1)) hc.2]
  have hbits := NearCubicGates.Close.WorkerArith.WorkerBounds.nbl_le_self
    (StageCertTests.certificateMetadata p c.kind).length
  have hmb : natBitLength (StageCertTests.certificateMetadata p c.kind).length≤258*A := by omega
  have hcube := Nat.pow_le_pow_left hL 3
  have hA2 : A≤A^2 := by nlinarith
  have hA3 : A^2≤A^3 := by nlinarith
  have hA4 : A^3≤A^4 := by nlinarith
  change countCoreCost c p (StageCertTests.scheduleHint p)≤10^8*A^4
  unfold countCoreCost
  nlinarith only [hA,hL,hP,hn,ht,hmb,hcube,hA2,hA3,hA4]

/-- The selected scalar-bootstrap source execution in
`prop:time`, paper/paper.tex, has polynomial
cost in the literal original call word, uniformly over witnesses. -/
theorem count_source_polynomial (B1 B2 : ℕ) :
    PreparedPolynomial (B1 := B1) (B2 := B2) (fun r =>
      3*(countCoreCost r.call r.selected.1 (StageCertTests.scheduleHint r.selected.1)+11)+2) := by
  have hm : PreparedPolynomial (B1 := B1) (B2 := B2) (fun r => prepScheduleMass r.call r.selected.1) :=
    (((((((PreparedPolynomial.callLength.add (PreparedPolynomial.const 1)).add
      (PreparedPolynomial.hint.add (PreparedPolynomial.const 1))).add
        ((PreparedPolynomial.scalar .k).add (PreparedPolynomial.const 1))).add
          ((PreparedPolynomial.scalar .chainLength).add (PreparedPolynomial.const 1))).add
            PreparedPolynomial.parameterReader).add PreparedPolynomial.arityBits).add
              PreparedPolynomial.kindBits).add (PreparedPolynomial.const 1)
  have hh : PreparedPolynomial (B1 := B1) (B2 := B2) (fun r =>
      3*(10^8*(prepScheduleMass r.call r.selected.1)^4+11)+2) :=
    ((PreparedPolynomial.const 3).mul (((PreparedPolynomial.const (10^8)).mul (hm.pow 4)).add
      (PreparedPolynomial.const 11))).add (PreparedPolynomial.const 2)
  exact hh.mono fun r => by have h := countCoreCost_le_mass r.call r.selected.1;omega

/-- The real selected compiled scalar bootstrap of `prop:time`,
paper/paper.tex, pays all cold setup, copied
preparation bytes, decoder work and head returns. -/
theorem count_prepared_budget_polynomial (B1 B2 : ℕ) :
    PreparedPolynomial (B1 := B1) (B2 := B2)
      (fun r => countHeaderBudget B1 B2 (r.call,r.witness)) := by
  have hN : PreparedPolynomial (B1 := B1) (B2 := B2)
      (fun r => countHeaderSteps B1 B2 (r.call,r.witness)) := by
    convert count_source_polynomial B1 B2 using 1
    funext r
    simp only [countHeaderSteps,r.dispatched]
  have hG := PreparedPolynomial.compilationScale (B1 := B1) (B2 := B2)
  have hI := PreparedPolynomial.inputLength (B1 := B1) (B2 := B2)
  have hupper : PreparedPolynomial (B1 := B1) (B2 := B2) (fun r =>
      10^6*((countHeaderSteps B1 B2 (r.call,r.witness)+1)*
        Gof StageRecovery.packetCallee (StageCertTests.prepScheduleSizes B1 B2) (leadOnes r.word)^2)+
          10*r.word.length) :=
    ((PreparedPolynomial.const (10^6)).mul ((hN.add (PreparedPolynomial.const 1)).mul (hG.pow 2))).add
      ((PreparedPolynomial.const 10).mul hI)
  refine hupper.mono ?_
  intro r
  exact NearCubicGates.Close.CellsPack.lang_le2 StageRecovery.packetCallee
    (StageCertTests.prepScheduleSizes B1 B2) r.word (countHeaderSteps B1 B2 (r.call,r.witness))

/-- The actual count bootstrap in `prop:time`, paper/paper.tex, has polynomial cost on every call and witness,
including default initialization, the entire bounded preparation
source, and all real scalar output and cleanup work. -/
theorem countHeaderPolyCost (B1 B2 : ℕ) :
    Program.PolyCost (fun c w => countHeaderBudget B1 B2 (c,w)) := by
  obtain ⟨K,e,hK⟩ := count_prepared_budget_polynomial B1 B2
  let z := StageCertTests.prepScheduleSizes B1 B2
  let P := 200*(Cells.ParameterArithmetic.preparationCoefficient B1+5)
  let C0 := 10^6*(51*Gof StageRecovery.packetCallee z 0^2)+10*P
  let d := B1+12
  refine ⟨K+C0,e+d,fun c w => ?_⟩
  have hbase : 1≤(callWord c).length+1 := by omega
  cases hd : Program.dispatch B1 B2 c with
  | none =>
    have hlead : leadOnes (countWord B1 B2 (c,w))=0 := by
      unfold countWord Program.prepWord Program.stageWord
      rw [hd]
      rfl
    have hb := NearCubicGates.Close.CellsPack.lang_le2 StageRecovery.packetCallee z
      (countWord B1 B2 (c,w)) 50
    have hbudget : countHeaderBudget B1 B2 (c,w)≤
        10^6*(51*Gof StageRecovery.packetCallee z 0^2)+10*(countWord B1 B2 (c,w)).length := by
      simpa only [countHeaderBudget,countHeaderSteps,hd,hlead] using hb
    have hword : (countWord B1 B2 (c,w)).length≤P*((callWord c).length+1)^d :=
      Cells.all_calls_prepWord_length B1 B2 c w
    have hp : 1≤((callWord c).length+1)^d := Nat.one_le_pow _ _ hbase
    have hcoarse : countHeaderBudget B1 B2 (c,w)≤C0*((callWord c).length+1)^d := by
      dsimp [C0]
      nlinarith
    exact hcoarse.trans (Nat.mul_le_mul (by omega)
      (Nat.pow_le_pow_right hbase (by omega)))
  | some p =>
    have hs := hK (PreparedScheduleRequest.mk c w p hd)
    exact hs.trans (Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right hbase (by omega)))

end NearQuarticWires.StageCertificateControl
