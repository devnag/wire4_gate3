import Proof.Quartic.StagePrint.EntryRetainFull
import Proof.Quartic.StagePrint.EntryEmptyFields
import Proof.Quartic.StagePrint.EntryMemory

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint.EntryFormat
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open NearCubicWires.WireExponent3_5.CompilerMachine

/-- `lem:print`, paper/paper.tex: only the
four literal finite context fields are acquired before the next entry. -/
def contextReader : St VV MM :=
  .seq (GreedyEntry.retainField 0 callLengthVar)
  (.seq (GreedyEntry.retainField 1 baseLengthVar)
  (.seq (GreedyEntry.retainField StageLift.preparedStore StageLift.preparedLength)
  (.seq (GreedyEntry.retainField 3 (66:Fin VV)) (readEmptyFields 7))))

def contextReaderScratch : List (Fin VV) :=
  [t0,t1,StageFormulaMetadata.payloadLengthVar,callLengthVar,baseLengthVar,
    StageLift.preparedLength,(66:Fin VV),vJ]

/-- `lem:print`, paper/paper.tex: the common
source has been physically retained with real field lengths, leaving
the Terms store empty for the next actual finite entry. -/
structure ContextMemory {modular : Bool} (r : Request modular) (a : DS VV MM) : Prop where
  callBits : a.ram 0=(frame (callWord r.header.call)).map Bool.toNat
  baseBits : a.ram 1=(frame ((Header.baseHeaderValues r.header).flatMap natWord)).map Bool.toNat
  countBits : a.ram StageLift.preparedStore=r.countsWord.map Bool.toNat
  callLength : a.env callLengthVar=(frame (callWord r.header.call)).length
  baseLength : a.env baseLengthVar=(frame ((Header.baseHeaderValues r.header).flatMap natWord)).length
  countLength : a.env StageLift.preparedLength=r.countsWord.length
  termsEmpty : a.ram 7=[]
  termsCursor : a.rc 7=0

/-- `lem:print`, paper/paper.tex: context
acquisition consumes exactly its eleven original framed fields, with
linear actual byte cost and no scan of the following entry. -/
theorem contextReader_run {modular : Bool} (C : Ctx) (r : Request modular)
    (rest : List Bool) (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip=r.contextWord++rest)
    (hblank : ∀ s,a.ram s=[] ∧ a.rc s=0)
    (hfit : Fits C r)
    (hgeometry : ([r.header.call.n,r.header.parameters.r,r.header.parameters.b,
      r.header.parameters.s].flatMap natWord).length<2^C.Wd) :
    Hs C contextReader a
      (10*((frame (callWord r.header.call)).length+
        (frame ((Header.baseHeaderValues r.header).flatMap natWord)).length+
        r.countsWord.length+([r.header.call.n,r.header.parameters.r,r.header.parameters.b,
          r.header.parameters.s].flatMap natWord).length)+51) (fun z =>
      C.inp.drop z.ip=rest ∧ ContextMemory r z ∧ CursorBounds z ∧ Cst z ∧
      z.out=a.out ∧ Fr a z contextReaderScratch) := by
  let f0:=frame (callWord r.header.call)
  let f1:=frame ((Header.baseHeaderValues r.header).flatMap natWord)
  let f2:=r.countsWord
  let f3:=[r.header.call.n,r.header.parameters.r,r.header.parameters.b,r.header.parameters.s].flatMap natWord
  have hin0 : C.inp.drop a.ip=frame f0++(frame f1++(frame f2++(frame f3++
      (List.replicate 7 false++rest)))) := by
    simpa only [Request.contextWord,Top.loadRec,f0,f1,f2,f3,frame,List.append_assoc,
      List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append] using hin
  unfold contextReader
  refine Hx.hs (Hs.then (GreedyEntry.retainField_full_run C 0 callLengthVar (by decide)
    f0 _ a hc hin0 (by rw [(hblank 0).1,(hblank 0).2];rfl) hfit.call) ?_)
  rintro b ⟨bl,_bp,bi,br,brc,brest,bc,bfr⟩ n0 hn0
  have bin : C.inp.drop b.ip=frame f1++(frame f2++(frame f3++(List.replicate 7 false++rest))) := by
    rw [bi];exact drop_adv hin0
  have bempty1 : b.ram 1=[] ∧ b.rc 1=0 := by
    rw [br,brc];simpa (config:={decide:=true}) using hblank (1:Fin MM)
  refine Hs.then (GreedyEntry.retainField_full_run C 1 baseLengthVar (by decide)
    f1 _ b bc bin (by rw [bempty1.1,bempty1.2];rfl) hfit.base) ?_
  rintro d ⟨dl,_dp,di,dr,drc,drest,dc,dfr⟩ n1 hn1
  have din : C.inp.drop d.ip=frame f2++(frame f3++(List.replicate 7 false++rest)) := by
    rw [di];exact drop_adv bin
  have dempty9 : d.ram StageLift.preparedStore=[] ∧ d.rc StageLift.preparedStore=0 := by
    rw [dr,drc,br,brc]
    simpa (config:={decide:=true}) [StageLift.preparedStore] using hblank StageLift.preparedStore
  refine Hs.then (GreedyEntry.retainField_full_run C StageLift.preparedStore StageLift.preparedLength
    (by decide) f2 _ d dc din (by rw [dempty9.1,dempty9.2];rfl) hfit.counts) ?_
  rintro e ⟨el,_ep,ei,er,erc,erest,ec,efr⟩ n2 hn2
  have ein : C.inp.drop e.ip=frame f3++(List.replicate 7 false++rest) := by
    rw [ei];exact drop_adv din
  have eempty3 : e.ram 3=[] ∧ e.rc 3=0 := by
    rw [er,erc,dr,drc,br,brc]
    simpa (config:={decide:=true}) [StageLift.preparedStore] using hblank (3:Fin MM)
  refine Hs.then (GreedyEntry.retainField_full_run C 3 (66:Fin VV) (by decide)
    f3 _ e ec ein (by rw [eempty3.1,eempty3.2];rfl) hgeometry) ?_
  rintro f ⟨_fl,_fp,fi,fr,frc,frest,fc,ffr⟩ n3 hn3
  have fin : C.inp.drop f.ip=List.replicate 7 false++rest := by rw [fi];exact drop_adv ein
  refine Hs.last (readEmptyFields_run C 7 rest f fc fin) ?_
  rintro z ⟨zi,zrest,zc,zfr⟩ n4 hn4
  have zr : z.ram=f.ram:=congrArg (fun t=>t.2.1) zrest
  have zrc : z.rc=f.rc:=congrArg (fun t=>t.2.2.1) zrest
  have zram : z.ram=Function.update (Function.update (Function.update (Function.update a.ram
      0 (f0.map Bool.toNat)) 1 (f1.map Bool.toNat)) StageLift.preparedStore
        (f2.map Bool.toNat)) 3 (f3.map Bool.toNat) := by
    rw [zr,fr,eempty3.1,List.nil_append,er,dempty9.1,List.nil_append,dr,
      bempty1.1,List.nil_append,br,(hblank 0).1,List.nil_append]
  have zcursor : z.rc=Function.update (Function.update (Function.update (Function.update a.rc
      0 f0.length) 1 f1.length) StageLift.preparedStore f2.length) 3 f3.length := by
    rw [zrc,frc,eempty3.2,Nat.zero_add,erc,dempty9.2,Nat.zero_add,drc,
      bempty1.2,Nat.zero_add,brc,(hblank 0).2,Nat.zero_add]
  refine ⟨⟨?_,?_,?_,zc,?_,?_⟩,?_⟩
  · rw [zi];exact drop_adv fin
  · constructor
    · rw [zram];simp (config:={decide:=true}) [StageLift.preparedStore,f0]
    · rw [zram];simp (config:={decide:=true}) [StageLift.preparedStore,f1]
    · rw [zram];simp (config:={decide:=true}) [StageLift.preparedStore,f2]
    · rw [zfr _ (by decide),ffr _ (by decide),efr _ (by decide),dfr _ (by decide)]
      exact bl
    · rw [zfr _ (by decide),ffr _ (by decide),efr _ (by decide)]
      exact dl
    · rw [zfr _ (by decide),ffr _ (by decide)]
      exact el
    · rw [zram];simp (config:={decide:=true}) [StageLift.preparedStore,(hblank 7).1]
    · rw [zcursor];simp (config:={decide:=true}) [StageLift.preparedStore,(hblank 7).2]
  · intro s
    rw [zram,zcursor]
    by_cases h0 : s=0
    · subst s;simp (config:={decide:=true}) [StageLift.preparedStore]
    by_cases h1 : s=1
    · subst s;simp (config:={decide:=true}) [StageLift.preparedStore]
    by_cases h9 : s=StageLift.preparedStore
    · subst s;simp (config:={decide:=true}) [StageLift.preparedStore]
    by_cases h3 : s=3
    · subst s;simp (config:={decide:=true}) [StageLift.preparedStore]
    simp only [Function.update_of_ne h0,Function.update_of_ne h1,
      Function.update_of_ne h9,Function.update_of_ne h3]
    rw [(hblank s).1,(hblank s).2]
    simp
  · exact (congrArg Prod.fst zrest).trans ((congrArg Prod.fst frest).trans
      ((congrArg Prod.fst erest).trans ((congrArg Prod.fst drest).trans (congrArg Prod.fst brest))))
  · exact (bfr.weaken (by simp [contextReaderScratch])).trans
      ((dfr.weaken (by simp [contextReaderScratch])).trans
      ((efr.weaken (by simp [contextReaderScratch])).trans
      ((ffr.weaken (by simp [contextReaderScratch])).trans (zfr.weaken (by simp [contextReaderScratch])))))
  · dsimp only [f0,f1,f2,f3] at hn0 hn1 hn2 hn3
    omega

end NearQuarticWires.StagePrint.EntryFormat
