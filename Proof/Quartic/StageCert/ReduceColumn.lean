import Proof.Quartic.StageCert.ReadTest
import Proof.Quartic.StageCert.TableWord
import Proof.Gates.Cells.Loop

set_option autoImplicit false

namespace NearQuarticWires.StageCert
open NearCubicGates.Close.Cells
open NearCubicWires NearCubicWires.RepairRepresentation

/-- `sec:algorithm`, paper/paper.tex: strict-test count and cursor. -/
def testCount : Fin VV := ⟨44, by decide⟩
def testIndex : Fin VV := ⟨45, by decide⟩

/-- `sec:algorithm`, paper/paper.tex: the physical record body
reads one signed moment, tests it, and advances the record cursor. -/
def reduceBody : St VV MM :=
  .seq readTest (.seq strictTest (.op (.inc testIndex)))

/-- `sec:algorithm`, paper/paper.tex: the physical column reducer
visits all strict moment tests in their stored order. -/
def reduceTests : St VV MM := .loop (.lt testIndex testCount) reduceBody

/-- `sec:algorithm`, paper/paper.tex: the finite register frame
of the strict-test reduction loop. -/
def reducerScratch : List (Fin VV) :=
  [testIndex,testSign,testMagnitude,testBound,testAccept] ++ rdNatT

/-- `sec:algorithm`, paper/paper.tex: exact state after reducing
a column, with no assumptions on the signs of its moments. -/
structure Reduced (C : Ctx) (a b : DS VV MM) (rs : List MomentRecord) (rest : List Bool) : Prop where
  cst : Cst b
  tail : C.inp.drop b.ip = rest
  out : b.out = a.out
  count : b.env testCount = a.env testCount
  index : b.env testIndex = a.env testIndex + rs.length
  accept : b.env testAccept = if columnPass rs then a.env testAccept else 0
  keep : Fr a b reducerScratch

/-- `eq:testX`–`eq:testPhi`, paper/paper.tex: the actual
column loop implements conjunction of every literal strict test with linear
record count and polynomial bit cost. -/
theorem reduceTests_run (C : Ctx) (rs : List MomentRecord) :
    ∀ (a : DS VV MM), Cst a → ∀ (rest : List Bool),
    C.inp.drop a.ip = rs.flatMap momentRecordWord ++ rest →
    a.env testIndex + rs.length = a.env testCount →
    a.env testCount < 2^C.Wd →
    (∀ r ∈ rs,
      natBitLength (if r.1 < 0 then 1 else 0)+2 ≤ C.Wd ∧
      natBitLength r.1.natAbs+2 ≤ C.Wd ∧ natBitLength r.2+2 ≤ C.Wd) →
    Hs C reduceTests a (rs.length*(90*C.Wd+120)+2)
      (fun b => Reduced C a b rs rest) := by
  classical
  induction rs with
  | nil =>
    intro a hc rest hin hi hn hw
    have ht : Cnd.eval a (.lt testIndex testCount) = false := by simp [Cnd.eval]; simp at hi; omega
    refine ⟨a, 2, Ex.loopF (by norm_num [Cnd.wf, testIndex, testCount]) ht, by simp, ?_⟩
    exact ⟨hc, by simpa using hin, rfl, rfl, by simp, by simp [columnPass], Fr.refl _ _⟩
  | cons r rs ih =>
    intro a hc rest hin hi hn hw
    have hwr := hw r (by simp)
    have ht : Cnd.eval a (.lt testIndex testCount) = true := by
      simp only [Cnd.eval, decide_eq_true_eq]
      simp only [List.length_cons] at hi
      omega
    obtain ⟨b, nb, eb, hbCost, hb⟩ := readTest_run C a hc r.1 r.2
      (rs.flatMap momentRecordWord ++ rest)
      (by simpa [List.flatMap_cons, momentRecordWord, List.append_assoc] using hin)
      hwr.1 hwr.2.1 hwr.2.2
    obtain ⟨e, ne, ee, heCost, he⟩ := strictTest_run C b hb.cst r.1 r.2 hb.sign hb.magnitude hb.bound
    have heCst : Cst e := Cst.of_fr hb.cst he.2.2 (by decide)
    have heI : e.env testIndex = a.env testIndex :=
      (he.2.2 testIndex (by decide)).trans (hb.frame testIndex (by decide))
    have heN : e.env testCount = a.env testCount :=
      (he.2.2 testCount (by decide)).trans (hb.frame testCount (by decide))
    have hinc : e.env testIndex+1 < 2^C.Wd := by simp only [List.length_cons] at hi; omega
    let f := e.set testIndex (e.env testIndex+1)
    have ef : Ex C (.op (.inc testIndex)) e f 1 := Ex.op (OpEx.inc testIndex e hinc)
    have ebody : Ex C reduceBody a f (nb+(ne+1+1)+1) := Ex.seq eb (Ex.seq ee ef)
    have hfCst : Cst f := Cst.of_fr heCst (Fr.set e _ (List.mem_singleton_self _)) (by decide)
    have hfTail : C.inp.drop f.ip = rs.flatMap momentRecordWord ++ rest := by
      change C.inp.drop e.ip = _
      have heip : e.ip = b.ip := congrArg Prod.fst he.2.1
      rw [heip]
      exact hb.tail
    have hfN : f.env testCount = a.env testCount := by
      change (e.set testIndex _).env testCount = _
      rw [DS.set_env_ne _ _ (by decide), heN]
    have hfI : f.env testIndex = a.env testIndex+1 := by simp [f, heI]
    have hstepKeep : Fr a f reducerScratch := by
      exact Fr.trans (hb.frame.weaken (by intro y hy; simp only [reducerScratch,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *; tauto))
        (Fr.trans (he.2.2.weaken (by intro y hy; simp only [reducerScratch,rdNatT,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *; tauto))
          (Fr.set e _ (by simp [reducerScratch])))
    obtain ⟨g, ng, eg, hgCost, hg⟩ := ih f hfCst rest hfTail
      (by simp only [List.length_cons] at hi; omega) (by omega)
      (fun t ht => hw t (by simp [ht]))
    refine ⟨g, nb+(ne+1+1)+1+ng+2,
      Ex.loopT (by norm_num [Cnd.wf, testIndex, testCount]) ht ebody eg, ?_, ?_⟩
    · simp only [List.length_cons]
      have hs : natBitLength (if r.1<0 then 1 else 0)+natBitLength r.1.natAbs+natBitLength r.2 ≤ 3*C.Wd := by omega
      nlinarith
    · refine ⟨hg.cst, hg.tail, ?_, hg.count.trans hfN, ?_, ?_, hstepKeep.trans hg.keep⟩
      · have heout : e.out = b.out := congrArg (fun p => p.2.1) he.2.1
        exact hg.out.trans (heout.trans hb.out)
      · rw [hg.index, hfI]
        simp only [List.length_cons]
        omega
      · rw [hg.accept]
        have haF : f.env testAccept = if r.1<(r.2:ℤ) then a.env testAccept else 0 := by
          change (e.set testIndex _).env testAccept = _
          rw [DS.set_env_ne _ _ (by decide), he.1, hb.frame testAccept (by decide)]
        rw [haF]
        simp only [columnPass, List.all_cons, recordPass, Bool.and_eq_true, decide_eq_true_eq]
        split_ifs <;> simp_all

end NearQuarticWires.StageCert
