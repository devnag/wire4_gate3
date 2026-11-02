import Proof.Quartic.StagePrint.EntryPrefixRead
import Proof.Quartic.StagePrint.EntryMetadata
import Proof.Quartic.StagePrint.EntryCompute
import Proof.Quartic.StagePrint.EntryWriter

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint.EntryFormat
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats

/-- `lem:print`, paper/paper.tex: the actual
cold word is read once before its unchanged existing Tuple input is
written; no following source, output length or decoded field is supplied. -/
def readerProgram (modular : Bool) : St VV MM :=
  .seq prefixReader (.seq readEntryFields
    (.seq (computeWidths modular) (GreedyEntry.retainField 7 termsLengthVar)))

/-- `prop:time`, paper/paper.tex: acquisition
is linear in actual retained field bits plus binary source metadata. -/
noncomputable def readerSteps {modular : Bool} (r : Request modular) : ℕ :=
  prefixSteps r+30*(natBitLength r.walkCode.val+natBitLength r.degree+natBitLength r.scale)+
    5*Nat.size r.header.call.n+5*natBitLength r.scale+10*(termsWord r.terms).length+290

/-- `lem:print`, paper/paper.tex: every retained
byte, measured length and computed width required by the complete
writer arises from the actual literal cold source. -/
theorem readerProgram_run {modular : Bool} (C : Ctx) (r : Request modular)
    (a : DS VV MM) (hc : Cst a) (hin : C.inp.drop a.ip=r.word)
    (hblank : ∀ s,a.ram s=[] ∧ a.rc s=0) (hfit : InputFits C r) :
    Hs C (readerProgram modular) a (readerSteps r) (fun z=>Ready r z ∧ z.out=a.out) := by
  unfold readerProgram
  refine Hx.hs (Hs.then (prefixReader_run C r
    (natWord r.walkCode.val++natWord r.degree++natWord r.scale++frame (termsWord r.terms))
    a hc (by simpa only [Request.word,List.append_assoc] using hin) hblank hfit) ?_)
  rintro b ⟨bn,bin,bmem,bcur,bc,bo,bfr⟩ n0 hn0
  refine Hs.then (readEntryFields_run C r.walkCode.val r.degree r.scale
    (frame (termsWord r.terms)) b bc bin hfit.indexRead hfit.degreeRead hfit.scaleRead) ?_
  rintro d ⟨dindex,ddegree,dscale,din,drest,dc,dfr⟩ n1 hn1
  have dr : d.ram=b.ram:=congrArg (fun t=>t.2.1) drest
  have drc : d.rc=b.rc:=congrArg (fun t=>t.2.2.1) drest
  have dmem : ContextMemory r d:=bmem.transport dr drc
    (dfr _ (by decide)) (dfr _ (by decide)) (dfr _ (by decide))
  have dcur : CursorBounds d := by intro s;rw [dr,drc];exact bcur s
  have dn : d.env Header.arity=r.header.call.n := by rw [dfr _ (by decide),bn]
  refine Hs.then (computeWidths_run C r d dc dn ddegree dscale hfit) ?_
  rintro e ⟨ew,esh,ec,efr⟩ n2 hn2
  have ei : e.ip=d.ip:=congrArg (fun t=>t.1) esh
  have eo : e.out=d.out:=congrArg (fun t=>t.2.1) esh
  have er : e.ram=d.ram:=congrArg (fun t=>t.2.2.1) esh
  have erc : e.rc=d.rc:=congrArg (fun t=>t.2.2.2.1) esh
  have emem : ContextMemory r e:=dmem.transport er erc
    (efr _ (by decide)) (efr _ (by decide)) (efr _ (by decide))
  have ecur : CursorBounds e := by intro s;rw [er,erc];exact dcur s
  have eindex : e.env indexVar=r.walkCode.val := by rw [efr _ (by decide),dindex]
  have edegree : e.env GreedyEntry.degreeVar=r.degree := by rw [efr _ (by decide),ddegree]
  have ein : C.inp.drop e.ip=frame (termsWord r.terms)++[] := by
    simpa only [ei,List.append_nil] using din
  refine Hs.last (GreedyEntry.retainField_full_run C 7 termsLengthVar (by decide)
    (termsWord r.terms) [] e ec ein (by rw [emem.termsEmpty,emem.termsCursor];rfl)
    hfit.toFits.terms) ?_
  rintro z ⟨zl,_zpayload,_zi,zram,zrc,zrest,zc,zfr⟩ n3 hn3
  have zMemory : Memory r z := by
    constructor
    · rw [zram]
      simpa (config:={decide:=true}) using emem.callBits
    · rw [zram]
      simpa (config:={decide:=true}) using emem.baseBits
    · rw [zram]
      simpa (config:={decide:=true}) [StageLift.preparedStore] using emem.countBits
    · rw [zram,Function.update_self,emem.termsEmpty,List.nil_append]
    · rw [zfr _ (by decide)];exact emem.callLength
    · rw [zfr _ (by decide)];exact emem.baseLength
    · rw [zfr _ (by decide)];exact emem.countLength
    · exact zl
    · rw [zfr _ (by decide),eindex]
    · rw [zfr _ (by decide),edegree]
    · rw [zfr _ (by decide),ew]
  have zcur : CursorBounds z := by
    intro s
    rw [zram,zrc]
    by_cases hs : s=7
    · subst s
      simp only [Function.update_self,emem.termsEmpty,emem.termsCursor,List.nil_append,
        Nat.zero_add,List.length_map]
      rfl
    · rw [Function.update_of_ne hs,Function.update_of_ne hs]
      exact ecur s
  refine ⟨⟨⟨zMemory,zcur,zc⟩,?_⟩,?_⟩
  · exact (congrArg Prod.fst zrest).trans (eo.trans ((congrArg Prod.fst drest).trans bo))
  · unfold readerSteps
    omega

end NearQuarticWires.StagePrint.EntryFormat
