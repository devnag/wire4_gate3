import Proof.Quartic.StageCert.AppendColumns

set_option autoImplicit false

namespace NearQuarticWires.StageCert
open NearCubicGates.Close.Cells
open NearCubicGates.Close.CounterMachine.CellTablesProg (cstInit_spec)
open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Interfaces (listWord)

/-- `sec:algorithm`, paper/paper.tex: expanding the two exact
frames gives the byte string written by the physical certificate finisher. -/
theorem certTableOutput_expansion (r : CertTableRequest) :
    certTableOutput r = if r.doAppend then
      framedBody r.payload ++ certBitsBody r.columns ++ [true,false,false]
    else framedBody r.payload ++ [false] := by
  cases h : r.doAppend <;>
    simp [certTableOutput,h,frame_eq_body,certBitsBody,framedBody,List.append_assoc]

/-- `sec:algorithm`, paper/paper.tex: the physical global
certificate finisher computes the exact next-stage word from the complete
signed table stream. -/
theorem finishProgram_run (C : Ctx) (r : CertTableRequest)
    (hin : C.inp = certTableWord r) (hW : tableWidth r+4 ≤ C.Wd) :
    Hs C finishProgram (a0 : DS VV MM)
      (10^7*(r.payload.length+streamWork r.columns+tableWidth r+1)*(C.Wd+1))
      (fun b => b.out = certTableOutput r) := by
  have hfield (v : ℕ) (hv : v ∈ scalarFields r) : natBitLength v+2 ≤ C.Wd :=
    (scalar_height_lt_width r v hv).trans (by omega)
  have hPayload : natBitLength r.payload.length+2 ≤ C.Wd := hfield _ (by simp [scalarFields])
  have hFlag : natBitLength (if r.doAppend then 1 else 0)+2 ≤ C.Wd := hfield _ (by simp [scalarFields])
  have hCols : natBitLength r.columns.length+2 ≤ C.Wd := hfield _ (by simp [scalarFields])
  have hRecords : ∀ rs ∈ r.columns, natBitLength rs.length+2 ≤ C.Wd ∧
      ∀ t ∈ rs, natBitLength (if t.1<0 then 1 else 0)+2 ≤ C.Wd ∧
        natBitLength t.1.natAbs+2 ≤ C.Wd ∧ natBitLength t.2+2 ≤ C.Wd := by
    intro rs hrs
    refine ⟨hfield _ (column_count_field r rs hrs),?_⟩
    intro t ht
    obtain ⟨h1,h2,h3⟩ := moment_fields_mem r rs hrs t ht
    exact ⟨hfield _ h1,hfield _ h2,hfield _ h3⟩
  have hPayPow : r.payload.length < 2^C.Wd :=
    (lt_natBitLength r.payload.length).trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hHead : natBitLength (tableWidth r)+2 ≤ C.Wd := by
    have hn := Nat.log_le_self 2 (tableWidth r)
    unfold natBitLength
    omega
  have hBasePay : r.payload.length ≤
      (r.payload.length+streamWork r.columns+tableWidth r+1)*(C.Wd+1) := by
    exact (show r.payload.length ≤ r.payload.length+streamWork r.columns+tableWidth r+1 by omega).trans
      (Nat.le_mul_of_pos_right _ (by omega))
  have hBaseWidth : C.Wd+1 ≤
      (r.payload.length+streamWork r.columns+tableWidth r+1)*(C.Wd+1) :=
    Nat.le_mul_of_pos_left _ (by omega)
  have hBaseWork : (streamWork r.columns+1)*(C.Wd+1) ≤
      (r.payload.length+streamWork r.columns+tableWidth r+1)*(C.Wd+1) :=
    Nat.mul_le_mul_right _ (by omega)
  apply Hx.hs
  unfold finishProgram
  refine Hs.then (cstInit_spec C (by omega)) (fun a ha na hna => ?_)
  have hip : a.ip = 0 := congrArg Prod.fst ha.2.1
  have hout : a.out = [] := congrArg (fun p => p.2.1) ha.2.1
  let tail := natWord r.payload.length ++ r.payload ++
    natWord (if r.doAppend then 1 else 0) ++ listWord (listWord momentRecordWord) r.columns
  have hinHead : C.inp.drop a.ip = natWord (tableWidth r) ++ tail := by
    rw [hip,List.drop_zero,hin]
    simp only [certTableWord,tail,List.append_assoc]
  refine Hs.then (rdNatI_spec a ha.1 (tableWidth r) tail hinHead hHead)
    (fun b hb nb hnb => ?_)
  have hbCst : Cst b := cst_fr ha.1 hb.2.2.2.2
  have hbTail : C.inp.drop b.ip = tail := by rw [hb.2.2.1]; exact drop_adv hinHead
  refine Hs.then (readInto_run C b hbCst payloadLength (by decide) (by decide) r.payload.length
    (r.payload ++ natWord (if r.doAppend then 1 else 0) ++ listWord (listWord momentRecordWord) r.columns)
    (by simpa [tail,List.append_assoc] using hbTail) hPayload) (fun c hc nc hnc => ?_)
  refine Hs.then (hs_zero C payloadIndex c) (fun d hd nz hnz => ?_)
  subst d
  let start := c.set payloadIndex 0
  have hsCst : Cst start := Cst.of_fr hc.2.2.2.1
    (Fr.set _ _ (List.mem_singleton_self _)) (by decide)
  have hsI : start.env payloadIndex = 0 := by simp [start]
  have hsN : start.env payloadLength = r.payload.length := by
    rw [DS.set_env_ne _ _ (by decide)]
    exact hc.1
  refine Hs.then (copyPayload_run C r.payload start hsCst
    (natWord (if r.doAppend then 1 else 0) ++ listWord (listWord momentRecordWord) r.columns)
    (by simpa [start,List.append_assoc] using hc.2.1)
    (by rw [hsI,hsN]; simp) (by rw [hsN]; exact hPayPow)) (fun d hd nd hnd => ?_)
  refine Hs.then (readInto_run C d hd.cst appendFlag (by decide) (by decide)
    (if r.doAppend then 1 else 0) (listWord (listWord momentRecordWord) r.columns)
    hd.tail hFlag) (fun e he ne hne => ?_)
  have heCst : Cst e := he.2.2.2.1
  have heOut : e.out = framedBody r.payload := by
    rw [he.2.2.1,hd.out]
    change c.out ++ _ = _
    have hbo : b.out = a.out := congrArg Prod.fst hb.2.2.2.1
    rw [hc.2.2.1,hbo,hout,List.nil_append]
  cases hAppend : r.doAppend with
  | false =>
    have ht : Cnd.eval e (.eq appendFlag vZ) = true := by simp [Cnd.eval,he.1,hAppend,heCst.z]
    refine Hs.last (Hs.iteT (by norm_num [Cnd.wf,appendFlag,vZ]) ht (hs_emit C false e))
      (fun f hf nf hnf => ?_)
    subst f
    refine ⟨?_,?_⟩
    · rw [certTableOutput_expansion,hAppend]
      simp only [Bool.false_eq_true,if_false]
      rw [heOut]
    · nlinarith only [hna,hnb,hnc,hnz,hnd,hne,hnf,hHead,hPayload,hFlag,hBasePay,hBaseWidth,hBaseWork]
  | true =>
    have ht : Cnd.eval e (.eq appendFlag vZ) = false := by simp [Cnd.eval,he.1,hAppend,heCst.z]
    refine Hs.last (Hs.iteF (by norm_num [Cnd.wf,appendFlag,vZ]) ht
      (appendColumns_run C e heCst r.columns [] (by simpa using he.2.1) hCols hRecords))
      (fun f hf nf hnf => ?_)
    refine ⟨?_,?_⟩
    · rw [hf,heOut,certTableOutput_expansion,hAppend]
      rfl
    · nlinarith only [hna,hnb,hnc,hnz,hnd,hne,hnf,hHead,hPayload,hFlag,hBasePay,hBaseWidth,hBaseWork]

end NearQuarticWires.StageCert
