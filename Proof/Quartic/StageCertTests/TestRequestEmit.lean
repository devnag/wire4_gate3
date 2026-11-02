import Proof.Quartic.StageCertTests.MetadataEmit
import Proof.Gates.WorkerArith.GuessWordLengths

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertTests

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells

/-- `eq:testX`–`eq:testPhi`, paper/paper.tex:
the physical kind tag follows the literal moment-provider record codec. -/
def ThresholdKind.tag : ThresholdKind → ℕ
  | .population => 0 | .digit => 1 | .finalError => 2

/-- `sec:algorithm`, paper/paper.tex:
one actual test request computes its scalar threshold and emits
the complete five-field moment-provider metadata record. -/
def emitTestRequest (kind : ThresholdKind) : St VV MM :=
  .seq (setK testTagVar kind.tag)
    (.seq (thresholdPower kind) (emitMetadataFields metadataVariables))

/-- `sec:algorithm`, paper/paper.tex:
the request emitter changes only bounded arithmetic and codec scratch. -/
def testRequestScratch : List (Fin VV) :=
  [testTagVar,thresholdFactor,thresholdExponent,thresholdBase,thresholdVar,a1,c4,vJ,t3,t5,t6,t7,t8,t9]

/-- `eq:testX`–`eq:testPhi` and `prop:time`, paper/paper.tex: one complete provider request derives its
threshold from real retained parameters, preserving every loop index. -/
theorem emitTestRequest_spec (C : Ctx) (a : DS VV MM) (p : Cells.Parameters)
    (kind : ThresholdKind) (j : Fin 2) (code : Fin 256) (position B : ℕ) (hc : Cst a)
    (hfields : ∀ field : ScheduleField, a.env field.variable = field.value p)
    (hj : a.env testCircuitVar = j.val) (hs : a.env signOrdinal = code.val)
    (hr : a.env testDigitVar = position)
    (hsmall : 8 < 2^C.Wd) (hexp : 8*p.k < 2^C.Wd)
    (hbase : kind.field.value p+kind.increment < 2^C.Wd)
    (hpower : kind.threshold p+1 < 2^C.Wd)
    (hB : 10 ≤ B) (hW : 2 ≤ C.Wd) (hBfit : B+2 < 2^C.Wd)
    (hposition : natBitLength position ≤ B) (hthreshold : natBitLength (kind.threshold p) ≤ B) :
    Hs C (emitTestRequest kind) a (7*(p.k*kind.multiplier)+200*B+300) (fun b =>
      b.out = a.out ++ (TestMetadata.mk kind.tag j.val code.val position (kind.threshold p)).word ∧
      (b.ip,b.ram,b.rc,b.kin,b.kout,b.kc) = (a.ip,a.ram,a.rc,a.kin,a.kout,a.kc) ∧
      Cst b ∧ Fr a b testRequestScratch) := by
  have htag : kind.tag ≤ 2 := by cases kind <;> decide
  have htagbits : natBitLength kind.tag ≤ 2 :=
    NearCubicGates.Close.WorkerArith.WorkerBounds.nbl_le_of_lt (by decide) (by omega)
  have hjbits : natBitLength j.val ≤ 1 :=
    NearCubicGates.Close.WorkerArith.WorkerBounds.nbl_le_of_lt (by decide) (by have := j.isLt;omega)
  have hsbits : natBitLength code.val ≤ 8 :=
    NearCubicGates.Close.WorkerArith.WorkerBounds.nbl_le_of_lt (by decide) code.isLt
  unfold emitTestRequest
  refine (Hs.seq (t2 := 7*(p.k*kind.multiplier)+200*B+290)
    (setK_spec testTagVar (by decide) kind.tag a (by omega))
    fun b ⟨hbt,hbsh,hbfr⟩ => ?_).mono (by omega) (fun _ h => h)
  have hbc : Cst b := Cst.of_fr hc hbfr (by decide)
  have hbfields : ∀ field : ScheduleField, b.env field.variable = field.value p := by
    intro field
    rw [hbfr _ (by cases field <;> decide),hfields]
  refine (Hs.seq (t2 := 200*B+249)
    (thresholdPower_spec C b p kind hbc hbfields hsmall hexp hbase hpower)
    fun d ⟨hdb,hdsh,hdc,hdfr⟩ => ?_).mono (by omega) (fun _ h => h)
  have hdt : d.env testTagVar = kind.tag := by rw [hdfr _ (by decide),hbt]
  have hdj : d.env testCircuitVar = j.val := by rw [hdfr _ (by decide),hbfr _ (by decide),hj]
  have hds : d.env signOrdinal = code.val := by rw [hdfr _ (by decide),hbfr _ (by decide),hs]
  have hdr : d.env testDigitVar = position := by rw [hdfr _ (by decide),hbfr _ (by decide),hr]
  have hfit : ∀ x ∈ metadataVariables, natBitLength (d.env x)+2 < 2^C.Wd := by
    intro x hx
    simp only [metadataVariables,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · rw [hdt];omega
    · rw [hdj];omega
    · rw [hds];omega
    · rw [hdr];omega
    · rw [hdb];omega
  refine (emitTestMetadata_spec C d hdc
    ⟨kind.tag,j.val,code.val,position,kind.threshold p⟩ hdt hdj hds hdr hdb hW hfit).mono (by
      change 40*(natBitLength kind.tag+natBitLength j.val+natBitLength code.val+
        natBitLength position+natBitLength (kind.threshold p))+216 ≤ 200*B+249
      omega) ?_
  rintro e ⟨heo,her,hec,hefr⟩
  have hsame := Same.of_sh (hdsh.trans hbsh)
  have hrest : (d.ip,d.ram,d.rc,d.kin,d.kout,d.kc) = (a.ip,a.ram,a.rc,a.kin,a.kout,a.kc) := by
    simp only [Prod.mk.injEq]
    exact ⟨hsame.ip,hsame.ram,hsame.rc,hsame.kin,hsame.kout,hsame.kc⟩
  refine ⟨?_,her.trans hrest,hec,?_⟩
  · rw [heo,hsame.out]
  · exact Fr.trans (Fr.weaken hbfr (by decide))
      (Fr.trans (Fr.weaken hdfr (by decide)) (Fr.weaken hefr (by decide)))

end NearQuarticWires.StageCertTests
