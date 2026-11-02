import Proof.Quartic.StageCert.FinishProgram

set_option autoImplicit false

namespace NearQuarticWires.StageCert
open NearCubicGates.Close.Cells
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces (listWord)

/-- `sec:algorithm`, paper/paper.tex: the complete in-stream
column loop and its two framing delimiters, with exact signed tests. -/
theorem appendColumns_run (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (columns : List (List MomentRecord)) (rest : List Bool)
    (hin : C.inp.drop a.ip = listWord (listWord momentRecordWord) columns ++ rest)
    (hN : natBitLength columns.length+2 ≤ C.Wd)
    (hR : ∀ rs ∈ columns, natBitLength rs.length+2 ≤ C.Wd ∧
      ∀ r ∈ rs, natBitLength (if r.1<0 then 1 else 0)+2 ≤ C.Wd ∧
        natBitLength r.1.natAbs+2 ≤ C.Wd ∧ natBitLength r.2+2 ≤ C.Wd) :
    Hs C appendColumns a (100000*(streamWork columns+1)*(C.Wd+1))
      (fun b => b.out = a.out ++ certBitsBody columns ++ [true,false,false]) := by
  have hlen : columns.length < 2^C.Wd :=
    (lt_natBitLength columns.length).trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
  apply Hx.hs
  unfold appendColumns
  refine Hs.then (readInto_run C a hc columnCount (by decide) (by decide) columns.length
    (columns.flatMap (listWord momentRecordWord) ++ rest)
    (by simpa [listWord,List.append_assoc] using hin) hN) (fun b hb nb hnb => ?_)
  refine Hs.then (hs_zero C columnIndex b) (fun c he nc hnc => ?_)
  subst c
  let start := b.set columnIndex 0
  have hsCst : Cst start := Cst.of_fr hb.2.2.2.1
    (Fr.set _ _ (List.mem_singleton_self _)) (by decide)
  have hsI : start.env columnIndex = 0 := by simp [start]
  have hsN : start.env columnCount = columns.length := by
    rw [DS.set_env_ne _ _ (by decide)]
    exact hb.1
  refine Hs.then (columnStream_run C columns start hsCst rest
    (by simpa [start] using hb.2.1) (by rw [hsI,hsN]; simp)
    (by rw [hsN]; exact hlen) hR) (fun d hd nd hnd => ?_)
  refine Hs.last (closeCertificate_run C d) (fun e he ne hne => ?_)
  refine ⟨?_,?_⟩
  · rw [he,hd.out]
    change (b.out ++ _) ++ _ = _
    rw [hb.2.2.1]
  · have hcols : columns.length ≤ streamWork columns := by
      clear hin hN hR hlen hb hnb hsCst hsI hsN hd hnd he hne
      induction columns with
      | nil => rfl
      | cons rs columns ih => simp only [List.length_cons,streamWork]; omega
    nlinarith

end NearQuarticWires.StageCert
