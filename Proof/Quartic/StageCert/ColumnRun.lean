import Proof.Quartic.StageCert.ReduceColumn
import Proof.Quartic.StageCert.RecordRun

set_option autoImplicit false

namespace NearQuarticWires.StageCert
open NearCubicGates.Close.Cells
open NearCubicGates.Close.CounterMachine.CellTablesProg (cstInit cstInit_spec)
open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Interfaces (listWord)

/-- `sec:algorithm`, paper/paper.tex: parse, reduce and output one
column of signed strict-test records. -/
def columnProgram : St VV MM :=
  .seq cstInit (.seq rdNatI (.seq (readInto testCount)
    (.seq (.op (.zero testIndex)) (.seq (.op (.copy testAccept v1))
      (.seq reduceTests finishTest)))))

/-- `sec:algorithm`, paper/paper.tex: the complete physical column
program writes the conjunction of all of its moment tests, with all parsing
and arithmetic operations included. -/
theorem columnProgram_run (C : Ctx) (W : ℕ) (rs : List MomentRecord)
    (hin : C.inp = natWord W ++ listWord momentRecordWord rs)
    (hW : W+4 ≤ C.Wd) (hWn : natBitLength rs.length ≤ W)
    (hWr : ∀ r ∈ rs, natBitLength (if r.1<0 then 1 else 0) ≤ W ∧
      natBitLength r.1.natAbs ≤ W ∧ natBitLength r.2 ≤ W) :
    Hs C columnProgram (a0 : DS VV MM) (1000*(rs.length+1)*(C.Wd+1))
      (fun d => d.out = frame [columnPass rs]) := by
  have hnW : natBitLength W ≤ W+1 := Nat.add_le_add_right (Nat.log_le_self 2 W) 1
  have hN : rs.length < 2^C.Wd :=
    (lt_natBitLength rs.length).trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
  apply Hx.hs
  unfold columnProgram
  refine Hs.then (cstInit_spec C (by omega)) (fun a ha na hna => ?_)
  have hip : a.ip = 0 := congrArg Prod.fst ha.2.1
  have hout : a.out = [] := congrArg (fun p => p.2.1) ha.2.1
  refine Hs.then (rdNatI_spec a ha.1 W (listWord momentRecordWord rs)
    (by rw [hip, List.drop_zero, hin]) (by omega)) (fun b hb nb hnb => ?_)
  have hbCst := cst_fr ha.1 hb.2.2.2.2
  have hbTail : C.inp.drop b.ip = listWord momentRecordWord rs := by
    rw [hb.2.2.1]
    exact drop_adv (by rw [hip, List.drop_zero, hin])
  refine Hs.then (readInto_run C b hbCst testCount (by decide) (by decide)
    rs.length (rs.flatMap momentRecordWord) hbTail (by omega)) (fun c hc nc hnc => ?_)
  refine Hs.then (hs_zero C testIndex c) (fun d hd nd hnd => ?_)
  subst d
  have hdCst : Cst (c.set testIndex 0) :=
    Cst.of_fr hc.2.2.2.1 (Fr.set c _ (List.mem_singleton_self _)) (by decide)
  refine Hs.then (hs_copy C testAccept v1 (c.set testIndex 0) (by decide)) (fun e he ne hne => ?_)
  subst e
  let start := (c.set testIndex 0).set testAccept ((c.set testIndex 0).env v1)
  have hsCst : Cst start := Cst.of_fr hdCst
    (Fr.set _ _ (List.mem_singleton_self _)) (by decide)
  have hsI : start.env testIndex = 0 := by simp [start, DS.set, testIndex, testAccept]
  have hsN : start.env testCount = rs.length := by
    simp only [start, DS.set_env_ne _ _ (by decide : testCount ≠ testAccept),
      DS.set_env_ne _ _ (by decide : testCount ≠ testIndex)]
    exact hc.1
  have hsA : start.env testAccept = 1 := by simp [start, hdCst.one]
  have hsTail : C.inp.drop start.ip = rs.flatMap momentRecordWord ++ [] := by simpa [start] using hc.2.1
  refine Hs.then (reduceTests_run C rs start hsCst [] hsTail (by rw [hsI, hsN]; simp)
    (by rw [hsN]; exact hN) (fun r hr => by obtain ⟨h1,h2,h3⟩ := hWr r hr; omega))
    (fun f hf nf hnf => ?_)
  have hfA : f.env testAccept = if columnPass rs then 1 else 0 := by simpa only [hsA] using hf.accept
  refine Hs.last (finishTest_run C f hf.cst (columnPass rs) hfA) (fun g hg ng hng => ?_)
  refine ⟨?_, ?_⟩
  · have hbo : b.out = a.out := congrArg Prod.fst hb.2.2.2.1
    rw [hg, hf.out]
    change c.out ++ _ = _
    rw [hc.2.2.1, hbo, hout, List.nil_append]
  · nlinarith

end NearQuarticWires.StageCert
