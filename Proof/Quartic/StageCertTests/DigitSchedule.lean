import Proof.Quartic.StageCertTests.TestRequestEmit

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertTests

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells

/-- `eq:testE` and `sec:algorithm`, paper/paper.tex: one sign pattern requires one whole table for each
selected digit of the rate chain, in its exact ordinal order. -/
def digitMetadata (p : Cells.Parameters) (j : Fin 2) (code : Fin 256) (position : ℕ) : TestMetadata :=
  ⟨1,j.val,code.val,position,ThresholdKind.digit.threshold p⟩

/-- `eq:testE`, paper/paper.tex:
the complete digit test metadata sequence has the actual selected chain length. -/
def digitMetadataList (p : Cells.Parameters) (j : Fin 2) (code : Fin 256) : List TestMetadata :=
  List.ofFn fun position : Fin p.J => digitMetadata p j code position.val

/-- `sec:algorithm`, paper/paper.tex:
a physical counted loop generates every actual whole-table digit request. -/
def digitSchedule : St VV MM :=
  forS testDigitVar ScheduleField.chainLength.variable (emitTestRequest .digit)

/-- `sec:algorithm`, paper/paper.tex:
the digit loop retains every register outside its explicit scratch set. -/
def digitScheduleScratch : List (Fin VV) := testDigitVar :: testRequestScratch

/-- `eq:testE` and `prop:time`, paper/paper.tex: the actual chain loop emits the exact requests with
polynomial scheduling cost and no per-walk table enumeration. -/
theorem digitSchedule_spec (C : Ctx) (a : DS VV MM) (p : Cells.Parameters)
    (j : Fin 2) (code : Fin 256) (B : ℕ) (hc : Cst a)
    (hfields : ∀ field : ScheduleField, a.env field.variable = field.value p)
    (hj : a.env testCircuitVar = j.val) (hs : a.env signOrdinal = code.val)
    (hsmall : 8 < 2^C.Wd) (hexp : 8*p.k < 2^C.Wd)
    (hbase : p.hE < 2^C.Wd) (hpower : ThresholdKind.digit.threshold p+1 < 2^C.Wd)
    (hB : 10 ≤ B) (hW : 2 ≤ C.Wd) (hBfit : B+2 < 2^C.Wd)
    (hJbits : natBitLength p.J ≤ B) (hJfit : p.J < 2^C.Wd)
    (hthreshold : natBitLength (ThresholdKind.digit.threshold p) ≤ B) :
    Hs C digitSchedule a (p.J*(56*p.k+200*B+304)+4) (fun b =>
      b.out = a.out ++ (digitMetadataList p j code).flatMap TestMetadata.word ∧
      (b.ip,b.ram,b.rc,b.kin,b.kout,b.kc) = (a.ip,a.ram,a.rc,a.kin,a.kout,a.kc) ∧
      (∀ field : ScheduleField, b.env field.variable = field.value p) ∧
      b.env testCircuitVar = j.val ∧ b.env signOrdinal = code.val ∧ Cst b ∧
      Fr a b digitScheduleScratch) := by
  let requests := digitMetadataList p j code
  have hl : requests.length = p.J := List.length_ofFn
  let I : ℕ → DS VV MM → Prop := fun k b =>
    b.out = a.out ++ (requests.take k).flatMap TestMetadata.word ∧
    (b.ip,b.ram,b.rc,b.kin,b.kout,b.kc) = (a.ip,a.ram,a.rc,a.kin,a.kout,a.kc) ∧
    (∀ field : ScheduleField, b.env field.variable = field.value p) ∧
    b.env testCircuitVar = j.val ∧ b.env signOrdinal = code.val ∧ Cst b ∧
    Fr a b digitScheduleScratch
  unfold digitSchedule
  refine (forS_spec' testDigitVar ScheduleField.chainLength.variable (by decide)
    (emitTestRequest .digit) a p.J hJfit I (56*p.k+200*B+300)
    (fun k b v ⟨hbo,hbr,hbf,hbj,hbs,hbc,hfr⟩ => ?_)
    ⟨by simp,rfl,hfields,hj,hs,hc,Fr.refl _ _⟩ (hfields .chainLength) ?_).mono le_rfl ?_
  · refine ⟨hbo,hbr,?_,?_,?_,Cst.of_fr (T := [testDigitVar]) hbc (Fr.set _ _ (by decide)) (by decide),
      Fr.trans hfr (Fr.set _ _ (by simp [digitScheduleScratch]))⟩
    · intro field
      simpa (config := {decide := true}) [DS.set,show field.variable ≠ testDigitVar by cases field <;> decide] using hbf field
    · simpa (config := {decide := true}) [DS.set] using hbj
    · simpa (config := {decide := true}) [DS.set] using hbs
  · intro k hk b ⟨hbo,hbr,hbf,hbj,hbs,hbc,hfr⟩ hbctr hbn
    have hkbits : natBitLength k ≤ B :=
      NearCubicGates.Close.WorkerArith.WorkerBounds.nbl_le_of_lt (by omega)
        ((hk.trans (lt_natBitLength p.J)).trans_le (Nat.pow_le_pow_right (by decide) hJbits))
    have hstep := emitTestRequest_spec C b p .digit j code k B hbc hbf hbj hbs hbctr
      hsmall hexp hbase hpower hB hW hBfit hkbits hthreshold
    have heq : 7*(p.k*ThresholdKind.digit.multiplier)+200*B+300 = 56*p.k+200*B+300 := by
      simp only [ThresholdKind.multiplier];ring
    rw [heq] at hstep
    refine hstep.mono le_rfl ?_
    rintro d ⟨hdo,hdr,hdc,hdf⟩
    have hkr : k < requests.length := by omega
    have hrequest : requests[k] = digitMetadata p j code k := by simp [requests,digitMetadataList]
    refine ⟨⟨?_,hdr.trans hbr,?_,?_,?_,hdc,
      Fr.trans hfr (Fr.weaken hdf (by intro x hx;exact List.mem_cons_of_mem _ hx))⟩,
      by rw [hdf _ (by decide),hbctr],by rw [hdf _ (by decide),hbn]⟩
    · rw [hdo,hbo,List.take_succ_eq_append_getElem hkr,List.flatMap_append,
        List.flatMap_singleton,hrequest,List.append_assoc]
      rfl
    · intro field
      rw [hdf _ (by cases field <;> decide),hbf]
    · rw [hdf _ (by decide),hbj]
    · rw [hdf _ (by decide),hbs]
  · rintro b ⟨⟨hbo,hbr,hbf,hbj,hbs,hbc,hfr⟩,_,_⟩
    refine ⟨?_,hbr,hbf,hbj,hbs,hbc,hfr⟩
    simpa only [List.take_of_length_le (by omega : requests.length ≤ p.J)] using hbo

end NearQuarticWires.StageCertTests
