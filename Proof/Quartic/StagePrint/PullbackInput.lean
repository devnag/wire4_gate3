import Proof.Quartic.StagePrint.IndexedInput

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming (marks marks_append marks_length)
open NearCubicGates.Close NearCubicGates.Close.WordPrograms
open NearQuarticWires.Control

variable {ns nr : ℕ}

/-- `imp:pullback` and `lem:print`, paper/paper.tex: copy the actual canonical metadata and selected original row into one callee input, retaining both sources. -/
def writePullbackInput (A B X : Fin (ns+1)) (OP C D : Fin nr) : WMX ns nr :=
  .seq (copyLoop false A X OP C)
    (.seq (copyLoop false B X OP D)
      (.seq (.wm (emitC X OP false))
        (.seq (.wm (WM.rewind A C))
          (.seq (.wm (WM.rewind B D)) (.wm (WM.rewind X OP))))))

/-- `prop:time`, paper/paper.tex: metadata copying, row copying and all three rewinds are charged. -/
def pullbackInputCost (a b : List Bool) : ℕ := 200*(a.length+b.length+1)

/-- `imp:pullback` and `lem:print`, paper/paper.tex: the physical pullback request contains the untouched original signed row after the actual metadata bytes, with no decoded-row oracle. -/
theorem writePullbackInput_exec (cap : ℕ) (A B X : Fin (ns+1)) (hAB : A≠B)
    (hAX : A≠X) (hBX : B≠X) (OP C D : Fin nr)
    (hOC : OP≠C) (hOD : OP≠D) (hCD : C≠D)
    (σ : WState ns nr) (a b : List Bool)
    (hA : σ.st A=frame a) (hB : σ.st B=frame b)
    (hhA : σ.sh A=0) (hhB : σ.sh B=0) (hX : σ.st X=[]) (hhX : σ.sh X=0)
    (hzO : σ.val OP=0) (hzC : σ.val C=0) (hzD : σ.val D=0)
    (hcap : 4*(a.length+b.length)+4≤cap) :
    WXExec cap (writePullbackInput A B X OP C D) σ (σ.sets X (frame (a++b)))
      (pullbackInputCost a b) := by
  have e1:=copyLoop_exec cap σ A X OP C false hAX hOC [] a [false]
    (by simp [hA,Codec.frame_eq_marks]) hhA (by rfl) (by rw [hX,hhX];rfl)
    (by rw [hzO];omega) (by rw [hzC];omega)
  rw [bitCells_false] at e1
  let σ1:=copySt σ A X OP C a.length (marks a)
  have e2:=copyLoop_exec cap σ1 B X OP D false hBX hOD [] b [false]
    (by simp [σ1,copySt,hBX,hB,Codec.frame_eq_marks])
    (by simp [σ1,copySt,hBX,hAB.symm,hhB]) (by rfl)
    (by simp [σ1,copySt,hAX.symm,hX,hhX,marks_length])
    (by simp [σ1,copySt,hOC,hzO,marks_length];omega)
    (by simp [σ1,copySt,hOD.symm,hCD.symm,hzD];omega)
  rw [bitCells_false] at e2
  let σ2:=copySt σ1 B X OP D b.length (marks b)
  have e3:=emitC_spec cap X OP false σ2
    (by simp [σ2,σ1,copySt,hX,hhX,marks_length])
    (by simp [σ2,σ1,copySt,hOD,hOC,hzO,marks_length];omega)
  let σ3:=appendO σ2 X OP [false]
  have e4:=wrewind_spec cap A C (2*a.length) σ3
    (by simp [σ3,σ2,σ1,appendO,copySt,hOC.symm,hCD,hzC])
    (by simp [σ3,σ2,σ1,appendO,copySt,hOC.symm,hCD,hzC];omega)
  let σ4:=(σ3.setv C 0).seth A (σ3.sh A-2*a.length)
  have e5:=wrewind_spec cap B D (2*b.length) σ4
    (by simp [σ4,σ3,σ2,σ1,appendO,copySt,hCD.symm,hOD.symm,hzD])
    (by simp [σ4,σ3,σ2,σ1,appendO,copySt,hCD.symm,hOD.symm,hzD];omega)
  let σ5:=(σ4.setv D 0).seth B (σ4.sh B-2*b.length)
  have e6:=wrewind_spec cap X OP (2*a.length+2*b.length+1) σ5
    (by simp [σ5,σ4,σ3,σ2,σ1,appendO,copySt,hOD,hOC,hzO,marks_length])
    (by simp [σ5,σ4,σ3,σ2,σ1,appendO,copySt,hOD,hOC,hzO,marks_length];omega)
  refine (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq (WXExec.wm e3)
    (WXExec.seq (WXExec.wm e4) (WXExec.seq (WXExec.wm e5) (WXExec.wm e6)))))).cast cap ?_ ?_
  · apply WState.eq
    · funext i
      by_cases hiX : i=X
      · subst hiX;simp [σ5,σ4,σ3,σ2,σ1,appendO,copySt,hAX.symm,hBX.symm,hhX,marks_length]
      · by_cases hiA : i=A
        · subst hiA;simp [σ5,σ4,σ3,σ2,σ1,appendO,copySt,hiX,hAB,hAX,hhA]
        · by_cases hiB : i=B
          · subst hiB;simp [σ5,σ4,σ3,σ2,σ1,appendO,copySt,hiX,hiA,hBX,hhB]
          · simp [σ5,σ4,σ3,σ2,σ1,appendO,copySt,hiX,hiA,hiB]
    · funext i
      by_cases hiX : i=X
      · subst hiX;simp [σ5,σ4,σ3,σ2,σ1,appendO,copySt,hX,Codec.frame_eq_marks,NearCubicWires.RepairOrdinary.Streaming.marks_append,List.append_assoc]
      · simp [σ5,σ4,σ3,σ2,σ1,appendO,copySt,hiX]
    · funext i
      by_cases hiO : i=OP
      · subst hiO;simp [σ5,σ4,σ3,σ2,σ1,appendO,copySt,hOC,hOD,hzO]
      · by_cases hiC : i=C
        · subst hiC;simp [σ5,σ4,σ3,σ2,σ1,appendO,copySt,hiO,hCD,hzC]
        · by_cases hiD : i=D
          · subst hiD;simp [σ5,σ4,σ3,σ2,σ1,appendO,copySt,hiO,hiC,hzD]
          · simp [σ5,σ4,σ3,σ2,σ1,appendO,copySt,hiO,hiC,hiD]
    · rfl
  · unfold pullbackInputCost
    omega

end NearQuarticWires.StagePrint
