import Proof.Quartic.StagePrint.EntryFormatRequest
import Proof.Quartic.StagePrint.EntryStoredField
import Proof.Quartic.StagePrint.EntryContextWriter
import Proof.Quartic.StagePrint.EntryFramedNatural
import Proof.Quartic.StagePrint.EntryWidthComplete

set_option autoImplicit false

namespace NearQuarticWires.StagePrint.EntryFormat

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats

/-- `lem:print`, paper/paper.tex: finite-field
lengths are measured during retention and remain outside every writer's
scratch variables. -/
def callLengthVar : Fin VV := 64
def baseLengthVar : Fin VV := 65
def termsLengthVar : Fin VV := 67

def writerScratch : List (Fin VV) :=
  [StageMain.CallSkip.lengthCounter,c0,t0,t3,t5,t6,t7,t8,t9]

/-- `lem:print`, paper/paper.tex: the physical
formatter retains only the real small context and one actual Terms
field, together with measured lengths and computed binary widths. -/
structure Memory {modular : Bool} (r : Request modular) (a : DS VV MM) : Prop where
  callBits : a.ram 0=(frame (callWord r.header.call)).map Bool.toNat
  baseBits : a.ram 1=(frame ((Header.baseHeaderValues r.header).flatMap natWord)).map Bool.toNat
  countBits : a.ram StageLift.preparedStore=r.countsWord.map Bool.toNat
  termBits : a.ram 7=(termsWord r.terms).map Bool.toNat
  callLength : a.env callLengthVar=(frame (callWord r.header.call)).length
  baseLength : a.env baseLengthVar=(frame ((Header.baseHeaderValues r.header).flatMap natWord)).length
  countLength : a.env StageLift.preparedLength=r.countsWord.length
  termLength : a.env termsLengthVar=(termsWord r.terms).length
  index : a.env indexVar=r.walkCode.val
  degree : a.env GreedyEntry.degreeVar=r.degree
  width : a.env GreedyEntry.widthVar=r.termRequest.stackWidth

/-- `lem:print`, paper/paper.tex: output
formatting preserves all retained semantic fields because none is a
codec scratch variable. -/
theorem Memory.preserved {modular : Bool} {r : Request modular} {a b : DS VV MM}
    (ha : Memory r a) (hr : b.ram=a.ram) (hf : Fr a b writerScratch) : Memory r b where
  callBits:=by rw [hr];exact ha.callBits
  baseBits:=by rw [hr];exact ha.baseBits
  countBits:=by rw [hr];exact ha.countBits
  termBits:=by rw [hr];exact ha.termBits
  callLength:=by rw [hf _ (by decide)];exact ha.callLength
  baseLength:=by rw [hf _ (by decide)];exact ha.baseLength
  countLength:=by rw [hf _ (by decide)];exact ha.countLength
  termLength:=by rw [hf _ (by decide)];exact ha.termLength
  index:=by rw [hf _ (by decide)];exact ha.index
  degree:=by rw [hf _ (by decide)];exact ha.degree
  width:=by rw [hf _ (by decide)];exact ha.width

/-- `lem:print`, paper/paper.tex: every retained
memory cursor lies inside the real finite store it scans. -/
def CursorBounds (a : DS VV MM) : Prop := ∀ s,a.rc s≤(a.ram s).length

/-- `lem:print`, paper/paper.tex: a paid full
field scan ends at its actual store length and preserves all other
valid store cursors. -/
theorem CursorBounds.updated {a b : DS VV MM} (ha : CursorBounds a)
    (store : Fin MM) (length : ℕ) (hr : b.ram=a.ram)
    (hc : b.rc=Function.update a.rc store length) (hl : length≤(a.ram store).length) :
    CursorBounds b := by
  intro other
  rw [hr,hc]
  by_cases h : other=store
  · subst other;simp only [Function.update_self];exact hl
  · rw [Function.update_of_ne h]
    exact ha other

/-- `lem:print`, paper/paper.tex: all finite
fields and the binary scalar codecs fit the actual machine's fixed
word width, independently of the number of following entries. -/
structure Fits {modular : Bool} (C : Ctx) (r : Request modular) : Prop where
  call : (frame (callWord r.header.call)).length<2^C.Wd
  base : (frame ((Header.baseHeaderValues r.header).flatMap natWord)).length<2^C.Wd
  counts : r.countsWord.length<2^C.Wd
  terms : (termsWord r.terms).length<2^C.Wd
  index : natBitLength r.walkCode.val+2<2^C.Wd
  degree : natBitLength r.degree+2<2^C.Wd
  width : natBitLength r.termRequest.stackWidth+2<2^C.Wd
  wordWidth : 2≤C.Wd

end NearQuarticWires.StagePrint.EntryFormat
