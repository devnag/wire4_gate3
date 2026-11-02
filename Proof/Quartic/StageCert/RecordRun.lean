import Proof.Quartic.StageCert.FinishTest
import Proof.Gates.CounterMachine.CellTablesMain2

set_option autoImplicit false

namespace NearQuarticWires.StageCert
open NearCubicGates.Close.Cells
open NearCubicGates.Close.CounterMachine.CellTablesProg (cstInit cstInit_spec)
open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary

/-- `sec:algorithm`, paper/paper.tex: a complete physical program
for one strict signed moment test, including parsing and framed output. -/
def recordProgram : St VV MM :=
  .seq cstInit (.seq rdNatI (.seq readTest
    (.seq (.op (.copy testAccept v1)) (.seq strictTest finishTest))))

/-- `sec:algorithm`, paper/paper.tex: the single-record program
writes exactly its strict-test bit, with a linear abstract operation bound. -/
theorem recordProgram_run (C : Ctx) (W : ℕ) (z : ℤ) (R : ℕ)
    (hin : C.inp = natWord W ++ NearCubicGates.Close.Interfaces.intWord z ++ natWord R)
    (hW : W+4 ≤ C.Wd)
    (hWs : natBitLength (if z < 0 then 1 else 0) ≤ W)
    (hWm : natBitLength z.natAbs ≤ W) (hWr : natBitLength R ≤ W) :
    Hs C recordProgram (a0 : DS VV MM) (1000*(W+1))
      (fun d => d.out = frame [decide (z < (R : ℤ))]) := by
  have hnW : natBitLength W ≤ W+1 := by
    unfold natBitLength
    exact Nat.add_le_add_right (Nat.log_le_self 2 W) 1
  apply Hx.hs
  unfold recordProgram
  refine Hs.then (cstInit_spec C (by omega)) (fun a ha na hna => ?_)
  have hip : a.ip = 0 := congrArg Prod.fst ha.2.1
  have hout : a.out = [] := congrArg (fun p => p.2.1) ha.2.1
  refine Hs.then (rdNatI_spec a ha.1 W
    (NearCubicGates.Close.Interfaces.intWord z ++ natWord R)
    (by rw [hip, List.drop_zero, hin, List.append_assoc]) (by omega)) (fun b hb nb hnb => ?_)
  have hcst : Cst b := cst_fr ha.1 hb.2.2.2.2
  have htail : C.inp.drop b.ip = NearCubicGates.Close.Interfaces.intWord z ++ natWord R := by
    rw [hb.2.2.1]
    exact drop_adv (by rw [hip, List.drop_zero, hin, List.append_assoc])
  refine Hs.then (readTest_run C b hcst z R [] (by simpa using htail)
    (by omega) (by omega) (by omega)) (fun c hc nc hnc => ?_)
  refine Hs.then (hs_copy C testAccept v1 c (by decide)) (fun d hd nd hnd => ?_)
  subst d
  have hdCst : Cst (c.set testAccept (c.env v1)) :=
    Cst.of_fr hc.cst (Fr.set c _ (List.mem_singleton_self _)) (by decide)
  have hdAcc : (c.set testAccept (c.env v1)).env testAccept = 1 := by simp [hc.cst.one]
  refine Hs.then (strictTest_run C _ hdCst z R
    (by simpa [DS.set, testSign, testAccept] using hc.sign)
    (by simpa [DS.set, testMagnitude, testAccept] using hc.magnitude)
    (by simpa [DS.set, testBound, testAccept] using hc.bound)) (fun e he ne hne => ?_)
  have heCst : Cst e := Cst.of_fr hdCst he.2.2 (by decide)
  have heAcc : e.env testAccept = if z < (R : ℤ) then 1 else 0 := by
    simpa only [hdAcc] using he.1
  refine Hs.last (finishTest_run C e heCst (decide (z < (R : ℤ)))
    (by simpa only [decide_eq_true_eq] using heAcc)) (fun f hf nf hnf => ?_)
  refine ⟨?_, ?_⟩
  · have heout : e.out = c.out := congrArg (fun p => p.2.1) he.2.1
    have hbout : b.out = a.out := congrArg Prod.fst hb.2.2.2.1
    rw [hf, heout, hc.out, hbout, hout, List.nil_append]
  · omega

end NearQuarticWires.StageCert
