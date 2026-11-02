import Proof.Quartic.StageCert.ColumnRun

set_option autoImplicit false

namespace NearQuarticWires.StageCert
open NearCubicGates.Close.Cells
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces (listWord)

/-- `sec:algorithm`, paper/paper.tex: the register frame of one
column reduction inside the global table scan. -/
def blockScratch : List (Fin VV) := testCount :: reducerScratch

/-- `sec:algorithm`, paper/paper.tex: the column body reads its
record count, resets the strict-test state and reduces all records. -/
def columnBlock : St VV MM :=
  .seq (readInto testCount) (.seq (.op (.zero testIndex))
    (.seq (.op (.copy testAccept v1)) reduceTests))

/-- `sec:algorithm`, paper/paper.tex: a completed column leaves
its bit in the acceptance register and preserves the global stream registers. -/
structure ColumnReduced (C : Ctx) (a b : DS VV MM) (rs : List MomentRecord) (rest : List Bool) : Prop where
  cst : Cst b
  tail : C.inp.drop b.ip = rest
  out : b.out = a.out
  accept : b.env testAccept = if columnPass rs then 1 else 0
  keep : Fr a b blockScratch

/-- `sec:algorithm`, paper/paper.tex: exact in-stream column
reduction, without restarting a physical machine or traversing later columns. -/
theorem columnBlock_run (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (rs : List MomentRecord) (rest : List Bool)
    (hin : C.inp.drop a.ip = listWord momentRecordWord rs ++ rest)
    (hN : natBitLength rs.length+2 ≤ C.Wd)
    (hR : ∀ r ∈ rs, natBitLength (if r.1<0 then 1 else 0)+2 ≤ C.Wd ∧
      natBitLength r.1.natAbs+2 ≤ C.Wd ∧ natBitLength r.2+2 ≤ C.Wd) :
    Hs C columnBlock a (1000*(rs.length+1)*(C.Wd+1))
      (fun b => ColumnReduced C a b rs rest) := by
  have hlen : rs.length < 2^C.Wd :=
    (lt_natBitLength rs.length).trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
  apply Hx.hs
  unfold columnBlock
  refine Hs.then (readInto_run C a hc testCount (by decide) (by decide) rs.length
    (rs.flatMap momentRecordWord ++ rest) (by simpa [listWord,List.append_assoc] using hin) hN)
    (fun b hb nb hnb => ?_)
  refine Hs.then (hs_zero C testIndex b) (fun c he nc hnc => ?_)
  subst c
  have hc : Cst (b.set testIndex 0) :=
    Cst.of_fr hb.2.2.2.1 (Fr.set _ _ (List.mem_singleton_self _)) (by decide)
  refine Hs.then (hs_copy C testAccept v1 (b.set testIndex 0) (by decide)) (fun d hd nd hnd => ?_)
  subst d
  let start := (b.set testIndex 0).set testAccept ((b.set testIndex 0).env v1)
  have hsCst : Cst start := Cst.of_fr hc
    (Fr.set _ _ (List.mem_singleton_self _)) (by decide)
  have hsI : start.env testIndex = 0 := by simp [start,DS.set,testIndex,testAccept]
  have hsN : start.env testCount = rs.length := by
    simp only [start,DS.set_env_ne _ _ (by decide : testCount≠testAccept),
      DS.set_env_ne _ _ (by decide : testCount≠testIndex)]
    exact hb.1
  have hsA : start.env testAccept = 1 := by simp [start,hc.one]
  have hsKeep : Fr a start blockScratch := by
    exact (hb.2.2.2.2.weaken (by intro y hy; simp only [blockScratch,reducerScratch,List.mem_cons,List.mem_append] at *; tauto)).trans
      ((Fr.set b _ (by simp [blockScratch,reducerScratch])).trans
        (Fr.set _ _ (by simp [blockScratch,reducerScratch])))
  refine Hs.last (reduceTests_run C rs start hsCst rest (by simpa [start] using hb.2.1)
    (by rw [hsI,hsN]; simp) (by rw [hsN]; exact hlen) hR) (fun e he ne hne => ?_)
  refine ⟨⟨he.cst,he.tail,he.out.trans hb.2.2.1,?_,hsKeep.trans (he.keep.weaken (fun y hy => List.mem_cons_of_mem _ hy))⟩,?_⟩
  · simpa only [hsA] using he.accept
  · nlinarith

end NearQuarticWires.StageCert
