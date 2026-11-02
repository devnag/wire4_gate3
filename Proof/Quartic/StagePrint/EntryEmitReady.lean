import Proof.Quartic.StagePrint.EntryMemory

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint.EntryFormat
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells

/-- `lem:print`, paper/paper.tex: all retained
fields and cursors remain valid through the finite output formatter. -/
def Ready {modular : Bool} (r : Request modular) (a : DS VV MM) : Prop :=
  Memory r a ∧ CursorBounds a ∧ Cst a

/-- `lem:print`, paper/paper.tex: a stored-field
emitter charges its full actual length and preserves every other
source field needed by later output fields. -/
theorem storedField_ready {modular : Bool} (C : Ctx) (r : Request modular)
    (store : Fin MM) (lengthVar : Fin VV) (hl : lengthVar≠StageMain.CallSkip.lengthCounter)
    (bits : List Bool) (a : DS VV MM) (ha : Ready r a)
    (hb : a.ram store=bits.map Bool.toNat) (hlen : a.env lengthVar=bits.length)
    (hfit : bits.length<2^C.Wd) :
    Hs C (emitStoredField store lengthVar) a (11*bits.length+10) (fun b =>
      b.out=a.out++frame bits ∧ Ready r b) := by
  have hrlen : (a.ram store).length=bits.length := by rw [hb,List.length_map]
  refine (emitStoredField_run C store lengthVar hl bits a ha.2.2 hb hlen hfit).mono
    (by
      have h: a.rc store≤bits.length := by simpa only [hrlen] using ha.2.1 store
      omega) ?_
  rintro b ⟨bo,_bi,br,brc,_bk,bc,bfr⟩
  refine ⟨bo,ha.1.preserved br (bfr.weaken (by simp [writerScratch])),
    ha.2.1.updated store bits.length br brc (by omega),bc⟩

/-- `lem:print`, paper/paper.tex: the measured
count context and actual walk ordinal are framed with a linear clock. -/
theorem contextField_ready {modular : Bool} (C : Ctx) (r : Request modular)
    (a : DS VV MM) (ha : Ready r a) (hfit : Fits C r) :
    Hs C contextFieldProgram a
      (27*r.countsWord.length+120*natBitLength r.walkCode.val+149) (fun b =>
      b.out=a.out++frame (r.countsWord++natWord r.walkCode.val) ∧ Ready r b) := by
  have hrlen : (a.ram StageLift.preparedStore).length=r.countsWord.length := by
    rw [ha.1.countBits,List.length_map]
  refine (contextFieldProgram_run C r.countsWord r.walkCode.val a ha.2.2
    ha.1.countBits ha.1.countLength ha.1.index hfit.counts hfit.wordWidth hfit.index).mono
      (by have h: a.rc StageLift.preparedStore≤r.countsWord.length := by
            simpa only [hrlen] using ha.2.1 StageLift.preparedStore
          omega) ?_
  rintro b ⟨bo,_bi,br,brc,_bk,bc,bfr⟩
  exact ⟨bo,ha.1.preserved br (bfr.weaken (by simp [writerScratch])),
    ha.2.1.updated StageLift.preparedStore r.countsWord.length br brc (by omega),bc⟩

/-- `lem:print`, paper/paper.tex: scalar
printing preserves the retained context, Terms and computed widths. -/
theorem framedScalar_ready {modular : Bool} (C : Ctx) (r : Request modular)
    (x : Fin VV) (hx : x≠t3) (value : ℕ) (a : DS VV MM) (ha : Ready r a)
    (hv : a.env x=value) (hW : 2≤C.Wd) (hfit : natBitLength value+2<2^C.Wd) :
    Hs C (emitFramedVariable x) a (120*natBitLength value+128) (fun b =>
      b.out=a.out++frame (natWord value) ∧ Ready r b) := by
  have er:=emitFramedVariable_run C x a ha.2.2 hx hW (by rwa [hv])
  rw [hv] at er
  refine er.mono (by omega) ?_
  rintro b ⟨bo,brest,bc,bfr⟩
  have br : b.ram=a.ram:=congrArg (fun t=>t.2.1) brest
  have brc : b.rc=a.rc:=congrArg (fun t=>t.2.2.1) brest
  refine ⟨bo,ha.1.preserved br (bfr.weaken (by simp [writerScratch])),?_,bc⟩
  intro store
  rw [brc,br]
  exact ha.2.1 store

end NearQuarticWires.StagePrint.EntryFormat
