import Proof.Quartic.StageCertNative.SkipFields
import Proof.Quartic.StageMainMask.StoredWord
import Proof.Quartic.StageFormulaMetadata.FiniteMachine
import Proof.Quartic.StageCertNative.JobArity

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells

/-- `lem:print`, paper/paper.tex: all fields
are correctness data for literal framed source bytes; their lengths
and the selected payload are not separate runtime fields. -/
structure FieldProjectionRequest (count : ℕ) where
  fields : List (List Bool)
  target : List Bool
  tail : List Bool
  prefix_length : fields.length=count

def FieldProjectionRequest.word {count : ℕ} (r : FieldProjectionRequest count) : List Bool :=
  r.fields.flatMap frame++frame r.target++r.tail

private theorem framed_fields_length (fields : List (List Bool)) :
    (fields.flatMap frame).length=2*(fields.map List.length).sum+fields.length := by
  induction fields with
  | nil=>simp
  | cons bits fields ih=>
    simp only [List.flatMap_cons,List.length_append,frame_length,List.map_cons,List.sum_cons,
      List.length_cons,ih]
    omega

/-- `lem:print`, paper/paper.tex: one fixed
field is extracted by marker-aware scans and a measured retained-word
copy, without a source-length or selected-payload input. -/
def fieldProjectionBody (count : ℕ) : St VV MM :=
  .seq (skipSourceFields count)
    (.seq (StagePrint.GreedyEntry.retainField 1 projectionLength)
      (StageMainMask.emitStoredWord 1 projectionLength))

theorem fieldProjectionBody_run {count : ℕ} (C : Ctx) (r : FieldProjectionRequest count)
    (a : DS VV MM) (hc : Cst a) (hin : C.inp.drop a.ip=r.word)
    (hwidth : r.word.length+10≤C.Wd)
    (hempty : ∀store,a.ram store=[] ∧ a.rc store=0) :
    Hs C (fieldProjectionBody count) a (100*(r.word.length+1))
      (fun z=>z.out=a.out++r.target) := by
  have hlen:=framed_fields_length r.fields
  have hword : r.word.length=(r.fields.flatMap frame).length+2*r.target.length+1+r.tail.length := by
    simp only [FieldProjectionRequest.word,List.length_append,frame_length]
    omega
  have ht : r.target.length<2^C.Wd :=
    lt_of_le_of_lt (by omega) Nat.lt_two_pow_self
  have hfields : ∀bits∈r.fields,bits.length<2^C.Wd := by
    intro bits hb
    have hh:=List.single_le_sum (fun _ _=>Nat.zero_le _) bits.length
      (List.mem_map.mpr ⟨bits,hb,rfl⟩)
    exact lt_of_le_of_lt (by omega) Nat.lt_two_pow_self
  unfold fieldProjectionBody
  have hprogram : skipSourceFields count=skipSourceFields r.fields.length :=
    congrArg skipSourceFields r.prefix_length.symm
  rw [hprogram]
  refine Hx.hs (Hs.then (skipSourceFields_run C r.fields (frame r.target++r.tail) a hc
    (by simpa only [FieldProjectionRequest.word,List.append_assoc] using hin)
    (by rw [(hempty 0).1,(hempty 0).2];rfl) hfields) ?_)
  rintro b ⟨bin,bo,_bcursor,bother,bc⟩ n0 hn0
  have b1 : b.ram 1=[] ∧ b.rc 1=0 := by
    have hh:=bother 1 (by decide)
    rw [(hempty 1).1,(hempty 1).2] at hh
    exact ⟨congrArg Prod.fst hh,congrArg Prod.snd hh⟩
  refine Hs.then (StagePrint.GreedyEntry.retainField_full_run C 1 projectionLength (by decide)
    r.target r.tail b bc bin (by rw [b1.1,b1.2];rfl) ht) ?_
  rintro d ⟨dl,_dp,_di,dr,drc,ds,dc,_df⟩ n1 hn1
  have d1 : d.ram 1=r.target.map Bool.toNat := by
    rw [dr,Function.update_self,b1.1,List.nil_append]
  refine Hs.last (StageMainMask.emitStoredWord_run C 1 projectionLength (by decide)
    r.target d dc d1 dl ht) ?_
  rintro z ⟨zo,_zi,_zk,_zr,_zrc,_zko,_zkc,_zc,_zf⟩ n2 hn2
  have dcursor : d.rc 1=r.target.length := by rw [drc,Function.update_self,b1.2];omega
  rw [dcursor] at hn2
  have doo : d.out=b.out := congrArg Prod.fst ds
  refine ⟨by rw [zo,doo,bo],?_⟩
  omega

def fieldProjectionProgram (count : ℕ) : St VV MM :=
  .seq initP (StageMain.framedOutputProgram (fieldProjectionBody count))

theorem fieldProjectionProgram_run {count : ℕ} (C : Ctx) (r : FieldProjectionRequest count)
    (hin : C.inp=r.word) (hwidth : r.word.length+10≤C.Wd) :
    Hs C (fieldProjectionProgram count) (a0 : DS VV MM) (300*(r.word.length+1)+8)
      (fun z=>z.out=frame r.target) := by
  unfold fieldProjectionProgram
  refine (Hs.seq (t2:=300*(r.word.length+1)+2)
    (initP_spec (C:=C) (a0 : DS VV MM) rfl rfl rfl
      (lt_trans (by omega) Nat.lt_two_pow_self)) ?_).mono (by omega) (fun _ h=>h)
  rintro a ⟨hc,hram,hrc,hip,hout,_,_,_,_⟩
  change a.ip=0 at hip
  change a.out=[] at hout
  obtain ⟨b,n,he,hn,ho⟩:=fieldProjectionBody_run C r a hc
    (by simp only [hip,List.drop_zero,hin]) hwidth
    (by intro store;rw [hram,hrc];exact ⟨rfl,rfl⟩)
  have hm : StageMain.markOutputState a=a := by
    unfold StageMain.markOutputState
    simp only [hout,List.flatMap_nil]
    rw [←hout]
  have hf:=StageMain.framedOutput_run he
  rw [hm] at hf
  refine ⟨{b with out:=frame b.out},3*n+2,hf,by omega,?_⟩
  change frame b.out=frame r.target
  rw [ho,hout,List.nil_append]

noncomputable def fieldProjectionBudget {count : ℕ} (r : FieldProjectionRequest count) : ℕ :=
  StageFormulaMetadata.finiteBudget StageRecovery.packetCallee VV MM r.word
    (300*(r.word.length+1)+8)

/-- `lem:print` and `prop:time`, paper/paper.tex: the cold ordinary field extractor includes actual
input measurement, binary allocation, all scans and exact output framing. -/
noncomputable def fieldProjectionWordFunction (count : ℕ) :
    WordFunction (FieldProjectionRequest count) FieldProjectionRequest.word
      (fun r=>frame r.target) fieldProjectionBudget :=
  StageFormulaMetadata.wordFunction_of_finite FieldProjectionRequest.word
    (fun r=>frame r.target) StageRecovery.packetCallee (fieldProjectionProgram count)
    (fun r=>300*(r.word.length+1)+8) (fun r=>by
      obtain ⟨b,n,he,hn,ho⟩:=fieldProjectionProgram_run
        (StageFormulaMetadata.finiteContext StageRecovery.packetCallee r.word) r rfl
        (by change r.word.length+10≤100*(r.word.length+1);omega)
      exact ⟨b,n,he,ho,hn⟩)

end NearQuarticWires.StageCertNative
