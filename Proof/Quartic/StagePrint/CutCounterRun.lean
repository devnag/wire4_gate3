import Proof.Quartic.StagePrint.CutCounterLoad

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint.CutCounter

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Expand.PolyTab
open NearCubicGates.Close.Recovery.HTParts

def Request.afterStride (r : Request) : WState 15 24 := r.loaded.setv 2 r.stride
def Request.counted (r : Request) : WState 15 24 :=
  (adv 2 14 0 1 r.afterStride [] r.stream.length).setv 5 r.cuts.length

/-- `lem:print`, paper/paper.tex: the cold
program loads the stream, measures its actual equality count and
serializes that count with the canonical binary natural codec. -/
noncomputable def program : WMX 15 24 :=
  .seq (.mach Top.loadM loadMap) <|
    .seq (unaryRegister 3 6 2) <|
      .seq (.wm (CutScan.countRows 2 countRegisters)) <|
        .seq (.wm (writeNatM 15 writeRegisters)) (.wm (emitC 15 13 false))

def Request.countCost (r : Request) : ℕ :=
  25*r.stream.length+r.cuts.length*(22*r.stride+11)+1
def Request.writeCost (r : Request) : ℕ :=
  (natBitLength r.cuts.length+10)*(100*r.cuts.length+200)
def Request.clock (r : Request) : ℕ :=
  r.loadCost+1+(16*r.stride+14+1+(r.countCost+1+(r.writeCost+1+7)))

theorem stride_run (r : Request) :
    WXExec r.capacity (unaryRegister 3 6 2) r.loaded r.afterStride (16*r.stride+14) := by
  apply unaryRegister_spec r.capacity 3 6 2 (by decide) r.loaded r.stride
  · rfl
  · rfl
  · rfl
  · rfl
  · unfold Request.capacity
    omega

theorem count_run (r : Request) :
    WExec r.capacity (CutScan.countRows 2 countRegisters) r.afterStride r.counted r.countCost := by
  have e:=CutScan.nativeCutCount_spec r.capacity 2 14 countRegisters (by decide)
    r.width r.fieldWidth r.cuts r.lengths [] [] rfl r.afterStride
    (by simp only [Request.afterStride,Request.loaded,Request.fields,WState.setv_st,
      Fin.val_ofNat,List.nil_append,List.append_nil];rfl)
    rfl rfl rfl rfl rfl
    (by change 0≤r.capacity;omega)
    (by change 0+r.stream.length≤r.capacity;unfold Request.capacity;omega)
    (by change r.stride≤r.capacity;unfold Request.capacity;omega)
    (by change 0+r.cuts.length≤r.capacity;unfold Request.capacity;omega)
  have hzero : r.afterStride.val (countRegisters 5)=0 := rfl
  rw [hzero,Nat.zero_add] at e
  rw [show countRegisters 0=(0 : Fin 24) from rfl,
    show countRegisters 1=(1 : Fin 24) from rfl,
    show countRegisters 5=(5 : Fin 24) from rfl] at e
  simpa only [Request.counted,Request.countCost,Request.stride,Request.stream] using e

theorem counted_zero (r : Request) (j : Fin 24)
    (h0 : j≠0) (h1 : j≠1) (h2 : j≠2) (h5 : j≠5) : r.counted.val j=0 := by
  unfold Request.counted
  rw [WState.setv_val,Function.update_of_ne h5,adv_val_other _ _ _ j h0 h1]
  simp only [Request.afterStride,WState.setv_val,Function.update_of_ne h2,Request.loaded]

theorem counted_count (r : Request) : r.counted.val 5=r.cuts.length := by
  simp only [Request.counted,WState.setv_val,Function.update_self]

theorem counted_output (r : Request) : r.counted.st 15=[] ∧ r.counted.sh 15=0 := by
  constructor
  · simp only [Request.counted,WState.setv_st,adv_st_other _ _ _ (15 : Fin 16) (by decide : (15:Fin 16)≠14),
      Request.afterStride,WState.setv_st,Request.loaded,show ¬(15:ℕ)<13 by decide,dif_neg,Request.lens]
    rfl
  · simp only [Request.counted,WState.setv_sh,adv_sh_other _ _ _ (15 : Fin 16) (by decide : (15:Fin 16)≠14)
      (by decide : (15:Fin 16)≠2),Request.afterStride,WState.setv_sh,Request.loaded]

/-- `lem:print` and `prop:time`, paper/paper.tex: the complete cold program produces its measured
count, including the zero-cut case, without a length oracle. -/
theorem program_run (r : Request) :
    ∃ final,WXExec r.capacity program (idealStart 15 24 r.word r.lens) final r.clock ∧
      final.st 15=frame (RepairRepresentation.natWord r.cuts.length) := by
  have el:=load_spec r.capacity r
  have es:=stride_run r
  have ec:=count_run r
  have hz : ∀ j : Fin 8,j≠0 → r.counted.val (writeRegisters j)=0 := by
    intro j hj
    fin_cases j
    all_goals first | (exfalso;exact hj rfl) | exact counted_zero r _ (by decide) (by decide) (by decide) (by decide)
  have hN : r.counted.val (writeRegisters 0)=r.cuts.length := counted_count r
  have hnbl : natBitLength r.cuts.length≤r.cuts.length+1 := by
    unfold natBitLength
    have h:=Nat.log_le_self 2 r.cuts.length
    omega
  have ew:=writeNatM_spec r.capacity 15 writeRegisters r.counted
    (hz 1 (by decide)) (hz 2 (by decide)) (hz 3 (by decide)) (hz 4 (by decide))
    (hz 5 (by decide)) (hz 6 (by decide))
    (by rw [(counted_output r).1,(counted_output r).2];rfl)
    (by rw [hN,hz 7 (by decide)];unfold Request.capacity;omega)
  rw [hN] at ew
  have h13 : r.counted.val 13=0 := counted_zero r 13 (by decide) (by decide) (by decide) (by decide)
  let middle:=appendO r.counted 15 13
    (RepairOrdinary.Streaming.marks (RepairRepresentation.natWord r.cuts.length))
  have hmhead : middle.sh 15=(middle.st 15).length := by
    simp [middle,appendO,(counted_output r).1,(counted_output r).2]
  have hmlen : middle.val 13=
      2*(RepairRepresentation.natWord r.cuts.length).length := by
    simp only [middle,appendO,Function.update_self,h13]
    simp [RepairOrdinary.Streaming.marks,NearCubicGates.Close.Codec.marks_length]
    omega
  have ee:=NearCubicGates.Close.Codec.emitBit_spec r.capacity 15 13 false middle hmhead
    (by rw [hmlen,NearCubicGates.Close.CounterAsm.natWord_len];unfold Request.capacity;omega)
  let final:=appendO middle 15 13 [false]
  refine ⟨final,?_,?_⟩
  · have e:=WXExec.seq el (WXExec.seq es (WXExec.seq (WXExec.wm ec)
      (WXExec.seq (WXExec.wm ew) (WXExec.wm ee))))
    exact e.mono (by rfl)
  · simp only [final,middle,appendO,Function.update_self,(counted_output r).1,List.nil_append]
    exact (NearCubicGates.Close.Codec.frame_eq_marks _).symm

end NearQuarticWires.StagePrint.CutCounter
