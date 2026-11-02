import Proof.Quartic.StagePrint.EntryReader

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open StagePrint StagePrint.EntryFormat

/-- `lem:print`, paper/paper.tex: the actual
entry reader computes both equality-header dimensions and stops at
the following framed raw equality stream without consuming it. -/
theorem readEqualityPrefix_run (C : Ctx) (r : Request false) (suffix : List Bool)
    (a : DS VV MM) (hc : Cst a) (hin : C.inp.drop a.ip=r.word++suffix)
    (hblank : ∀ s,a.ram s=[] ∧ a.rc s=0) (hfit : InputFits C r) :
    Hs C (readerProgram false) a (readerSteps r) (fun z=>
      z.env Header.arity=r.header.call.n ∧
      z.env GreedyEntry.widthVar=r.termRequest.stackWidth ∧
      C.inp.drop z.ip=suffix ∧ z.out=a.out ∧ Cst z) := by
  unfold readerProgram
  refine Hx.hs (Hs.then (prefixReader_run C r
    (natWord r.walkCode.val++natWord r.degree++natWord r.scale++frame (termsWord r.terms)++suffix)
    a hc (by simpa only [Request.word,List.append_assoc] using hin) hblank hfit) ?_)
  rintro b ⟨bn,bin,bmem,_bcur,bc,bo,_bfr⟩ n0 hn0
  refine Hs.then (readEntryFields_run C r.walkCode.val r.degree r.scale
    (frame (termsWord r.terms)++suffix) b bc
    (by simpa only [List.append_assoc] using bin)
    hfit.indexRead hfit.degreeRead hfit.scaleRead) ?_
  rintro d ⟨_dindex,ddegree,dscale,din,drest,dc,dfr⟩ n1 hn1
  have dr : d.ram=b.ram:=congrArg (fun t=>t.2.1) drest
  have drc : d.rc=b.rc:=congrArg (fun t=>t.2.2.1) drest
  have dn : d.env Header.arity=r.header.call.n := (dfr _ (by decide)).trans bn
  refine Hs.then (computeWidths_run C r d dc dn ddegree dscale hfit) ?_
  rintro e ⟨ew,esh,ec,efr⟩ n2 hn2
  have ei : e.ip=d.ip:=congrArg (fun t=>t.1) esh
  have eo : e.out=d.out:=congrArg (fun t=>t.2.1) esh
  have er : e.ram=d.ram:=congrArg (fun t=>t.2.2.1) esh
  have erc : e.rc=d.rc:=congrArg (fun t=>t.2.2.2.1) esh
  have en : e.env Header.arity=r.header.call.n := (efr _ (by decide)).trans dn
  have ein : C.inp.drop e.ip=frame (termsWord r.terms)++suffix := by rw [ei];exact din
  have eempty : e.ram 7=[] := by rw [er,dr];exact bmem.termsEmpty
  have ecur : e.rc 7=0 := by rw [erc,drc];exact bmem.termsCursor
  refine Hs.last (GreedyEntry.retainField_full_run C 7 termsLengthVar (by decide)
    (termsWord r.terms) suffix e ec ein (by rw [eempty,ecur];rfl)
    hfit.toFits.terms) ?_
  rintro z ⟨_zl,_zpayload,zi,_zram,_zrc,zrest,zc,zfr⟩ n3 hn3
  refine ⟨⟨(zfr _ (by decide)).trans en,(zfr _ (by decide)).trans ew,?_,?_,zc⟩,?_⟩
  · rw [zi,←List.drop_drop,ein]
    exact List.drop_left
  · exact (congrArg Prod.fst zrest).trans (eo.trans ((congrArg Prod.fst drest).trans bo))
  · unfold readerSteps
    omega

end NearQuarticWires.StageCertNative
