import Proof.Quartic.StageEqualityRows.Load

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageEqualityRows

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Recovery.HTParts
open StagePrint

def capacity (r : NativeStreamRequest) : ℕ :=
  loadCapacity r+100*(stream r).length+100*(width r+r.fieldWidth+r.cuts.length+1)+100

def countRegisters : Fin 6 ↪ Fin 24 :=
  ⟨fun i=>i.castAdd 18,by intro i j h;apply Fin.ext;exact congrArg (fun x : Fin 24=>x.val) h⟩

def afterWidth (r : NativeStreamRequest) : WState 15 24 := (loaded r).setv 14 (width r)
def afterFields (r : NativeStreamRequest) : WState 15 24 := (afterWidth r).setv 15 r.fieldWidth

def makeStride : WM 15 24 :=
  .seq (addTo 14 2 16) (.seq (addTo 14 2 16) (.seq (.inc 2) (.inc 2)))

def strideState (r : NativeStreamRequest) : WState 15 24 :=
  (afterFields r).setv 2 (2*width r+2)

def counted (r : NativeStreamRequest) : WState 15 24 :=
  (adv 2 14 0 1 (strideState r) [] (stream r).length).setv 5 r.cuts.length

def countCost (r : NativeStreamRequest) : ℕ :=
  25*(stream r).length+r.cuts.length*(22*(2*width r+2)+11)+1

/-- `lem:print`, paper/paper.tex: dense width
and original signed-field width are measured from their actual unary
source fields, without changing any original cut bytes. -/
theorem width_run (r : NativeStreamRequest) :
    WXExec (capacity r) (unaryRegister 3 6 14) (loaded r) (afterWidth r) (16*width r+14) := by
  apply unaryRegister_spec (capacity r) 3 6 14 (by decide) (loaded r) (width r)
  · rfl
  · rfl
  · rfl
  · rfl
  · unfold capacity
    omega

theorem fieldWidth_run (r : NativeStreamRequest) :
    WXExec (capacity r) (unaryRegister 4 6 15) (afterWidth r) (afterFields r) (16*r.fieldWidth+14) := by
  apply unaryRegister_spec (capacity r) 4 6 15 (by decide) (afterWidth r) r.fieldWidth
  · rfl
  · rfl
  · rfl
  · rfl
  · unfold capacity
    omega

/-- `lem:print`, paper/paper.tex: the actual
row stride is computed by two literal additions and two increments. -/
theorem makeStride_run (r : NativeStreamRequest) :
    WExec (capacity r) makeStride (afterFields r) (strideState r) (36*width r+16) := by
  let a:=afterFields r
  have hw : a.val 14=width r := rfl
  have h2 : a.val 2=0 := rfl
  have h16 : a.val 16=0 := rfl
  have e1:=addTo_spec (capacity r) (14 : Fin 24) 2 16 (by decide) (by decide) (by decide) a h16
    (by rw [hw];unfold capacity;omega) (by rw [h2,hw];unfold capacity;omega)
  let b:=a.setv 2 (width r)
  have e1' : WExec (capacity r) (addTo 14 2 16) a b (18*width r+3) := by
    simpa only [hw,h2,Nat.zero_add] using e1
  have e2:=addTo_spec (capacity r) (14 : Fin 24) 2 16 (by decide) (by decide) (by decide) b
    (by simp [b,h16]) (by simp [b,hw];unfold capacity;omega)
    (by simp [b,hw];unfold capacity;omega)
  let c:=b.setv 2 (2*width r)
  have e2' : WExec (capacity r) (addTo 14 2 16) b c (18*width r+3) := by
    simpa only [c,b,WState.setv_val,Function.update_self,
      Function.update_of_ne (by decide : (14 : Fin 24)≠2),hw,two_mul] using e2
  have e3:=WExec.inc (cap:=capacity r) (2 : Fin 24) c (by simp [c];unfold capacity;omega)
  let d:=c.setv 2 (c.val 2+1)
  have e4:=WExec.inc (cap:=capacity r) (2 : Fin 24) d (by simp [d,c];unfold capacity;omega)
  refine (e1'.seq (e2'.seq (e3.seq e4))).cast (capacity r) ?_ (by dsimp;omega)
  simp only [d,c,b,WState.setv_val,Function.update_self,wsetv_setv]
  rfl

/-- `lem:print` and `prop:time`, paper/paper.tex: the real field-framing scan counts precisely the
original equalities, including an empty bank. -/
theorem count_run (r : NativeStreamRequest) :
    WExec (capacity r) (CutScan.countRows 2 countRegisters) (strideState r) (counted r) (countCost r) := by
  have e:=CutScan.nativeCutCount_spec (capacity r) 2 14 countRegisters (by decide)
    (width r) r.fieldWidth r.cuts r.lengths [] [] rfl (strideState r)
    (by simp only [strideState,afterFields,afterWidth,WState.setv_st,
      loaded,fields,Fin.val_ofNat,List.nil_append,List.append_nil];rfl)
    rfl rfl rfl rfl rfl
    (by change 0≤capacity r;omega)
    (by change 0+(stream r).length≤capacity r;unfold capacity;omega)
    (by unfold capacity;omega)
    (by change 0+r.cuts.length≤capacity r;unfold capacity;omega)
  have hzero : (strideState r).val (countRegisters 5)=0 := rfl
  rw [hzero,Nat.zero_add] at e
  rw [show countRegisters 0=(0 : Fin 24) from rfl,
    show countRegisters 1=(1 : Fin 24) from rfl,
    show countRegisters 5=(5 : Fin 24) from rfl] at e
  exact e

end NearQuarticWires.StageEqualityRows
