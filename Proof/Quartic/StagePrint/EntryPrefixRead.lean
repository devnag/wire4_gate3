import Proof.Quartic.StagePrint.EntryInputFits
import Proof.Quartic.StagePrint.EntryContextRead
import Proof.Quartic.StageRecovery.PacketFields

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint.EntryFormat
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces

/-- `lem:print`, paper/paper.tex: retained
context data survive every later purely binary metadata calculation. -/
theorem ContextMemory.transport {modular : Bool} {r : Request modular}
    {a b : DS VV MM} (ha : ContextMemory r a)
    (hr : b.ram=a.ram) (hrc : b.rc=a.rc)
    (hcall : b.env callLengthVar=a.env callLengthVar)
    (hbase : b.env baseLengthVar=a.env baseLengthVar)
    (hcount : b.env StageLift.preparedLength=a.env StageLift.preparedLength) :
    ContextMemory r b where
  callBits:=by rw [hr];exact ha.callBits
  baseBits:=by rw [hr];exact ha.baseBits
  countBits:=by rw [hr];exact ha.countBits
  callLength:=hcall.trans ha.callLength
  baseLength:=hbase.trans ha.baseLength
  countLength:=hcount.trans ha.countLength
  termsEmpty:=by rw [hr];exact ha.termsEmpty
  termsCursor:=by rw [hrc];exact ha.termsCursor

/-- `lem:print`, paper/paper.tex: the original
arity is decoded before the finite context fields are retained. -/
def prefixReader : St VV MM :=
  .seq (StageRecovery.readVariable Header.arity) contextReader

/-- `prop:time`, paper/paper.tex: prefix
acquisition is linear in its actual finite original bytes and codecs. -/
def prefixSteps {modular : Bool} (r : Request modular) : ℕ :=
  30*natBitLength r.header.call.n+
    10*((frame (callWord r.header.call)).length+
      (frame ((Header.baseHeaderValues r.header).flatMap natWord)).length+
      r.countsWord.length+r.geometryField.length)+84

/-- `lem:print`, paper/paper.tex: the actual
original-arity-first source prefix produces the retained context and
stops exactly before the original indexed entry, with all cursor and
field lengths computed by the physical reader. -/
theorem prefixReader_run {modular : Bool} (C : Ctx) (r : Request modular)
    (rest : List Bool) (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip=natWord r.header.call.n++r.contextWord++rest)
    (hblank : ∀ s,a.ram s=[] ∧ a.rc s=0) (hfit : InputFits C r) :
    Hs C prefixReader a (prefixSteps r) (fun z=>
      z.env Header.arity=r.header.call.n ∧ C.inp.drop z.ip=rest ∧
      ContextMemory r z ∧ CursorBounds z ∧ Cst z ∧ z.out=a.out ∧
      Fr a z (Header.arity::(rdNatT++contextReaderScratch))) := by
  unfold prefixReader
  have er:=StageRecovery.readVariable_spec C a hc Header.arity (by decide) (by decide)
    r.header.call.n _ (by simpa only [List.append_assoc] using hin) hfit.arityRead
  refine (Hs.seq (t2:=10*((frame (callWord r.header.call)).length+
    (frame ((Header.baseHeaderValues r.header).flatMap natWord)).length+
    r.countsWord.length+r.geometryField.length)+51) er fun b ⟨bn,bi,brest,bc,bfr⟩=>?_).mono (by unfold prefixSteps;omega) (fun _ h=>h)
  have bin : C.inp.drop b.ip=r.contextWord++rest := by
    rw [bi,←List.drop_drop,hin]
    simp only [List.append_assoc,List.drop_left]
  have br : b.ram=a.ram:=congrArg (fun t=>t.2.1) brest
  have brc : b.rc=a.rc:=congrArg (fun t=>t.2.2.1) brest
  have bblank : ∀ s,b.ram s=[] ∧ b.rc s=0 := by intro s;rw [br,brc];exact hblank s
  refine (contextReader_run C r rest b bc bin bblank hfit.toFits hfit.geometry).mono le_rfl ?_
  rintro z ⟨zi,zm,zcur,zc,zo,zfr⟩
  refine ⟨?_,zi,zm,zcur,zc,zo.trans (congrArg Prod.fst brest),?_⟩
  · rw [zfr _ (by decide),bn]
  · exact (bfr.weaken (by simp [rdNatT,contextReaderScratch])).trans
      (zfr.weaken (by simp [rdNatT,contextReaderScratch]))

end NearQuarticWires.StagePrint.EntryFormat
