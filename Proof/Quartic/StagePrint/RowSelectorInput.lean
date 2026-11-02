import Proof.Quartic.StagePrint.PullbackInput
import Proof.Wire_3_5.PrimAsmCopyNat
import Proof.Wire_3_5.CompilerMachineTopLoad

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.CopyNat
open NearCubicWires.RepairOrdinary.Streaming (marks marks_length)
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close NearCubicGates.Close.WordPrograms
open NearQuarticWires.Control

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: the original-row selector's literal eleven-field setup contains only the actual child cache and actual unary child index. -/
def originalRowInput (cache index : List Bool) : List Bool :=
  Top.loadRec (cache++[false]) index [] [] [] [] [] [] [] [] []

/-- `lem:print`, paper/paper.tex: nested frame markers of the actual original-row setup are copied literally. -/
theorem originalRowInput_frame (cache index : List Bool) :
    frame (originalRowInput cache index)=
      marks (marks cache)++marks [true,false,false]++marks (marks index)++
        marks (List.replicate 10 false)++[false] := by
  simp [originalRowInput,Top.loadRec,Codec.frame_eq_marks,
    NearCubicWires.RepairOrdinary.Streaming.marks_append,marks,List.replicate_succ,List.append_assoc]

/-- `lem:print`, paper/paper.tex: original child-cache bytes and index bits are turned into the selector's full cold input before the call. -/
def writeOriginalRowInput (A B X : Fin (ns+1)) (OP C D : Fin nr) : WMX ns nr :=
  .seq (copyLoop true A X OP C)
    (.seq (.wm (emitWordM X OP [true,false,false]))
      (.seq (copyLoop true B X OP D)
        (.seq (.wm (emitWordM X OP (List.replicate 10 false)))
          (.seq (.wm (emitC X OP false))
            (.seq (.wm (WM.rewind A C))
              (.seq (.wm (WM.rewind B D)) (.wm (WM.rewind X OP))))))))

/-- `prop:time`, paper/paper.tex: every selector-input marker and every reset is included in its physical clock. -/
def originalRowInputCost (a b : List Bool) : ℕ := 400*(a.length+b.length+1)+400

/-- `lem:print`, paper/paper.tex: the actual child printer output is physically formatted for the existing original-row selector, without a supplied compiler record stream. -/
theorem writeOriginalRowInput_exec (cap : ℕ) (A B X : Fin (ns+1)) (hAB : A≠B)
    (hAX : A≠X) (hBX : B≠X) (OP C D : Fin nr)
    (hOC : OP≠C) (hOD : OP≠D) (hCD : C≠D)
    (σ : WState ns nr) (a b : List Bool)
    (hA : σ.st A=frame a) (hB : σ.st B=frame b)
    (hhA : σ.sh A=0) (hhB : σ.sh B=0) (hX : σ.st X=[]) (hhX : σ.sh X=0)
    (hzO : σ.val OP=0) (hzC : σ.val C=0) (hzD : σ.val D=0)
    (hcap : 4*(a.length+b.length)+100≤cap) :
    WXExec cap (writeOriginalRowInput A B X OP C D) σ (σ.sets X (frame (originalRowInput a b)))
      (originalRowInputCost a b) := by
  have e1:=copyLoop_exec cap σ A X OP C true hAX hOC [] a [false]
    (by simp [hA,Codec.frame_eq_marks]) hhA (by rfl) (by rw [hX,hhX];rfl)
    (by rw [hzO];omega) (by rw [hzC];omega)
  rw [bitCells_true] at e1
  let σ1:=copySt σ A X OP C a.length (marks (marks a))
  have e1b:=emitWordM_spec cap X OP [true,false,false] σ1
    (by simp [σ1,copySt,hX,hhX,marks_length])
    (by simp [σ1,copySt,hOC,hzO,marks_length];omega)
  let σ1b:=appendO σ1 X OP (marks [true,false,false])
  have e2:=copyLoop_exec cap σ1b B X OP D true hBX hOD [] b [false]
    (by simp [σ1b,σ1,appendO,copySt,hBX,hB,Codec.frame_eq_marks])
    (by simp [σ1b,σ1,appendO,copySt,hBX,hAB.symm,hhB]) (by rfl)
    (by simp [σ1b,σ1,appendO,copySt,hX,hhX,marks_length])
    (by simp [σ1b,σ1,appendO,copySt,hOC,hzO,marks_length];omega)
    (by simp [σ1b,σ1,appendO,copySt,hOD.symm,hCD.symm,hzD];omega)
  rw [bitCells_true] at e2
  let σ2:=copySt σ1b B X OP D b.length (marks (marks b))
  have e2b:=emitWordM_spec cap X OP (List.replicate 10 false) σ2
    (by simp [σ2,σ1b,σ1,appendO,copySt,hX,hhX,marks_length];omega)
    (by simp [σ2,σ1b,σ1,appendO,copySt,hOD,hOC,hzO,marks_length];omega)
  let σ2b:=appendO σ2 X OP (marks (List.replicate 10 false))
  have e3:=emitC_spec cap X OP false σ2b
    (by simp [σ2b,σ2,σ1b,σ1,copySt,appendO,hX,hhX,marks_length];omega)
    (by simp [σ2b,σ2,σ1b,σ1,appendO,copySt,hOD,hOC,hzO,marks_length];omega)
  let σ3:=appendO σ2b X OP [false]
  have e4:=wrewind_spec cap A C (2*a.length) σ3
    (by simp [σ3,σ2b,σ2,σ1b,σ1,appendO,copySt,hOC.symm,hCD,hzC])
    (by simp [σ3,σ2b,σ2,σ1b,σ1,appendO,copySt,hOC.symm,hCD,hzC];omega)
  let σ4:=(σ3.setv C 0).seth A (σ3.sh A-2*a.length)
  have e5:=wrewind_spec cap B D (2*b.length) σ4
    (by simp [σ4,σ3,σ2b,σ2,σ1b,σ1,appendO,copySt,hCD.symm,hOD.symm,hzD])
    (by simp [σ4,σ3,σ2b,σ2,σ1b,σ1,appendO,copySt,hCD.symm,hOD.symm,hzD];omega)
  let σ5:=(σ4.setv D 0).seth B (σ4.sh B-2*b.length)
  have e6:=wrewind_spec cap X OP (4*a.length+6+4*b.length+20+1) σ5
    (by simp [σ5,σ4,σ3,σ2b,σ2,σ1b,σ1,appendO,copySt,hOD,hOC,hzO,marks_length];omega)
    (by simp [σ5,σ4,σ3,σ2b,σ2,σ1b,σ1,appendO,copySt,hOD,hOC,hzO,marks_length];omega)
  refine (WXExec.seq e1 (WXExec.seq (WXExec.wm e1b) (WXExec.seq e2
    (WXExec.seq (WXExec.wm e2b) (WXExec.seq (WXExec.wm e3)
      (WXExec.seq (WXExec.wm e4) (WXExec.seq (WXExec.wm e5) (WXExec.wm e6)))))))).cast cap ?_ ?_
  · apply WState.eq
    · funext i
      by_cases hiX : i=X
      · subst hiX;simp [σ5,σ4,σ3,σ2b,σ2,σ1b,σ1,appendO,copySt,hAX.symm,hBX.symm,hhX,marks_length];omega
      · by_cases hiA : i=A
        · subst hiA;simp [σ5,σ4,σ3,σ2b,σ2,σ1b,σ1,appendO,copySt,hiX,hAB,hAX,hhA]
        · by_cases hiB : i=B
          · subst hiB;simp [σ5,σ4,σ3,σ2b,σ2,σ1b,σ1,appendO,copySt,hiX,hiA,hBX,hhB]
          · simp [σ5,σ4,σ3,σ2b,σ2,σ1b,σ1,appendO,copySt,hiX,hiA,hiB]
    · funext i
      by_cases hiX : i=X
      · subst hiX;simp [σ5,σ4,σ3,σ2b,σ2,σ1b,σ1,appendO,copySt,hX,originalRowInput_frame,List.append_assoc]
      · simp [σ5,σ4,σ3,σ2b,σ2,σ1b,σ1,appendO,copySt,hiX]
    · funext i
      by_cases hiO : i=OP
      · subst hiO;simp [σ5,σ4,σ3,σ2b,σ2,σ1b,σ1,appendO,copySt,hOC,hOD,hzO]
      · by_cases hiC : i=C
        · subst hiC;simp [σ5,σ4,σ3,σ2b,σ2,σ1b,σ1,appendO,copySt,hiO,hCD,hzC]
        · by_cases hiD : i=D
          · subst hiD;simp [σ5,σ4,σ3,σ2b,σ2,σ1b,σ1,appendO,copySt,hiO,hiC,hzD]
          · simp [σ5,σ4,σ3,σ2b,σ2,σ1b,σ1,appendO,copySt,hiO,hiC,hiD]
    · rfl
  · unfold originalRowInputCost
    norm_num only [List.length_cons,List.length_nil,List.length_replicate]
    omega

end NearQuarticWires.StagePrint
