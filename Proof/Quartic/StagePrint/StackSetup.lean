import Proof.Quartic.StagePrint.StackMachine

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.Expand.PolyTab
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.TabMachine
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicGates.Close.WordPrograms.SInt (encS)

/-- `lem:print`, paper/paper.tex: three physical extractions initialize distinct arithmetic words. -/
noncomputable def stackLoadProgram : WMX 44 26 :=
  .seq (.mach Top.loadM (stackLoadMap 0))
    (.seq (.mach Top.loadM (stackLoadMap 1)) (.mach Top.loadM (stackLoadMap 2)))

/-- `lem:print`, paper/paper.tex: the extraction program starts on the serialized input. -/
theorem stackLoadProgram_spec (cap : ℕ) (r : StackRequest) :
    WXExec cap stackLoadProgram (idealStart 44 26 r.word r.lens) (r.loaded 3)
      (r.loadCost+1+(r.loadCost+1+r.loadCost)) := by
  rw [← stackLoad_zero r]
  exact (stackLoad_spec cap r 0).seq ((stackLoad_spec cap r 1).seq (stackLoad_spec cap r 2))

/-- `lem:print`, paper/paper.tex: explicit tuple-count and stride reads. -/
def stackDimensions : WMX 44 26 :=
  .seq (unaryRegister 8 25 11) <|
    .seq (unaryRegister 8 25 23) <|
      .seq (unaryRegister 9 25 13) <|
        .seq (unaryRegister 9 25 15) <|
          .seq (unaryRegister 10 25 16) (unaryRegister 11 25 21)

/-- `lem:print`, paper/paper.tex: the resulting dimension registers, with all source heads reset. -/
def StackRequest.ready (r : StackRequest) : WState 44 26 :=
  ((((((r.loaded 3).setv 11 (r.m*(r.s+1))).setv 23 (r.m*(r.s+1))).setv 13 (r.s+1)).setv 15
    (r.s+1)).setv 16 r.m).setv 21 r.tuples.length

/-- `lem:print`, paper/paper.tex: all six reads are counted. -/
def StackRequest.dimensionCost (r : StackRequest) : ℕ :=
  (16*(r.m*(r.s+1))+14)+1+((16*(r.m*(r.s+1))+14)+1+
    ((16*(r.s+1)+14)+1+((16*(r.s+1)+14)+1+
      ((16*r.m+14)+1+(16*r.tuples.length+14)))))

/-- `lem:print`, paper/paper.tex: serialized dimensions are physically installed without altering tuple bytes. -/
theorem stackDimensions_spec (cap : ℕ) (r : StackRequest)
    (hM : r.m*(r.s+1)+1 ≤ cap) (hN : r.s+1+1 ≤ cap)
    (hm : r.m+1 ≤ cap) (hT : r.tuples.length+1 ≤ cap) :
    WXExec cap stackDimensions (r.loaded 3) r.ready r.dimensionCost := by
  let σ0 := r.loaded 3
  let σ1 := σ0.setv 11 (r.m*(r.s+1))
  let σ2 := σ1.setv 23 (r.m*(r.s+1))
  let σ3 := σ2.setv 13 (r.s+1)
  let σ4 := σ3.setv 15 (r.s+1)
  let σ5 := σ4.setv 16 r.m
  have a1 := unaryRegister_spec cap (8 : Fin 45) (25 : Fin 26) 11 (by decide) σ0
    (r.m*(r.s+1)) rfl rfl rfl rfl hM
  have a2 := unaryRegister_spec cap (8 : Fin 45) (25 : Fin 26) 23 (by decide) σ1
    (r.m*(r.s+1)) rfl rfl
    (by simp [σ1,σ0,StackRequest.loaded]) (by simp [σ1,σ0,StackRequest.loaded]) hM
  have a3 := unaryRegister_spec cap (9 : Fin 45) (25 : Fin 26) 13 (by decide) σ2
    (r.s+1) rfl rfl
    (by simp [σ2,σ1,σ0,StackRequest.loaded]) (by simp [σ2,σ1,σ0,StackRequest.loaded]) hN
  have a4 := unaryRegister_spec cap (9 : Fin 45) (25 : Fin 26) 15 (by decide) σ3
    (r.s+1) rfl rfl
    (by simp [σ3,σ2,σ1,σ0,StackRequest.loaded]) (by simp [σ3,σ2,σ1,σ0,StackRequest.loaded]) hN
  have a5 := unaryRegister_spec cap (10 : Fin 45) (25 : Fin 26) 16 (by decide) σ4
    r.m rfl rfl
    (by simp [σ4,σ3,σ2,σ1,σ0,StackRequest.loaded])
    (by simp [σ4,σ3,σ2,σ1,σ0,StackRequest.loaded]) hm
  have a6 := unaryRegister_spec cap (11 : Fin 45) (25 : Fin 26) 21 (by decide) σ5
    r.tuples.length rfl rfl
    (by simp [σ5,σ4,σ3,σ2,σ1,σ0,StackRequest.loaded])
    (by simp [σ5,σ4,σ3,σ2,σ1,σ0,StackRequest.loaded]) hT
  exact (a1.seq (a2.seq (a3.seq (a4.seq (a5.seq a6))))).cast cap rfl le_rfl

/-- `lem:print`, paper/paper.tex: distinct tuple, output, constant, and arithmetic tapes. -/
def stackStreams : Fin 14 ↪ Fin 45 :=
  ⟨![2,43,44,3,4,5,16,17,18,29,30,6,31,7],by decide⟩

/-- `lem:print`, paper/paper.tex: distinct stacking registers. -/
def stackRegisters : Fin 25 ↪ Fin 26 :=
  ⟨fun i => ⟨i.val,by have:=i.isLt;omega⟩,by
    intro i j h
    apply Fin.ext
    exact congrArg (fun x : Fin 26 => x.val) h⟩

/-- `lem:print`, paper/paper.tex: loaded binary constants satisfy the exact stacking invariant. -/
theorem stackReady_pre (r : StackRequest) :
    SPre stackStreams stackRegisters r.W (r.m*(r.s+1)) (r.s+1) r.m r.nums
      r.coefficient r.ready := by
  refine ⟨⟨[],by simp [StackRequest.ready,StackRequest.loaded,StackRequest.fields,stackStreams]⟩,
    rfl,rfl,by simp [StackRequest.ready,StackRequest.loaded,StackRequest.lens,stackStreams],?_,
    ⟨rfl,rfl⟩,⟨rfl,rfl⟩,⟨rfl,rfl⟩,?_,?_,?_⟩
  · intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact ⟨0,rfl,rfl⟩
  · intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  · simp [StackRequest.ready,stackRegisters]
  · simp [StackRequest.ready,stackRegisters]

end NearQuarticWires.StagePrint
