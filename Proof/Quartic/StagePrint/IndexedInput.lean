import Proof.Quartic.Control.Write
import Proof.Quartic.StagePrint.CallAppend

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming (marks marks_append marks_length)
open NearCubicGates.Close NearCubicGates.Close.WordPrograms
open NearCubicWires.RepairRepresentation (natWord)
open NearQuarticWires.Control

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: physically write an occurrence index and the retained original call on an empty callee tape. -/
def writeIndexedInput (IN X : Fin (ns+1)) (R : Fin 8 ↪ Fin nr) (C : Fin nr) : WMX ns nr :=
  .seq (.wm (writeNatM X R))
    (.seq (copyLoop false IN X (R 7) C)
      (.seq (.wm (emitC X (R 7) false))
        (.seq (.wm (WM.rewind IN C)) (.wm (WM.rewind X (R 7))))))

/-- `prop:time`, paper/paper.tex: the actual runtime index serialization and finite-call copy have one polynomial clock. -/
def writeIndexedCost (index sourceLength : ℕ) : ℕ := 10000*(index+1)^2+200*(sourceLength+1)

/-- `lem:print`, paper/paper.tex: one input writer retains the original call, preserves the occurrence counter, and resets all copy heads and registers. -/
theorem writeIndexedInput_exec (cap : ℕ) (IN X : Fin (ns+1)) (R : Fin 8 ↪ Fin nr) (C : Fin nr)
    (hIX : IN≠X) (hCR : ∀i,C≠R i) (σ : WState ns nr) (v : ℕ) (w : List Bool)
    (hv : σ.val (R 0)=v) (hz : ∀i,i≠0→σ.val (R i)=0) (hC : σ.val C=0)
    (hIN : σ.st IN=frame w) (hINh : σ.sh IN=0) (hX : σ.st X=[]) (hXh : σ.sh X=0)
    (hcap : v+8*natBitLength v+4*w.length+20≤cap) :
    WXExec cap (writeIndexedInput IN X R C) σ (σ.sets X (frame (natWord v++w)))
      (writeIndexedCost v w.length) := by
  have hOC : R 7≠C := (hCR 7).symm
  have hO : σ.val (R 7)=0 := hz 7 (by decide)
  have e1:=writeNatM_spec cap X R σ (hz 1 (by decide)) (hz 2 (by decide))
    (hz 3 (by decide)) (hz 4 (by decide)) (hz 5 (by decide)) (hz 6 (by decide))
    (by rw [hXh,hX];rfl) (by rw [hv,hO];omega)
  rw [hv] at e1
  let σ1:=appendO σ X (R 7) (marks (natWord v))
  have hNW : (natWord v).length=2*natBitLength v+1 := by
    exact NearCubicGates.Close.CounterAsm.natWord_len v
  have e2:=copyLoop_exec cap σ1 IN X (R 7) C false hIX hOC [] w [false]
    (by simp [σ1,appendO,hIX,hIN,Codec.frame_eq_marks])
    (by simp [σ1,appendO,hIX,hINh]) (by rfl)
    (by simp [σ1,appendO,hXh,hX])
    (by simp [σ1,appendO,hO,marks_length,hNW];omega)
    (by simp [σ1,appendO,hOC.symm,hC];omega)
  rw [bitCells_false] at e2
  let σ2:=copySt σ1 IN X (R 7) C w.length (marks w)
  have h2X : σ2.sh X=(σ2.st X).length := by
    simp [σ2,copySt,σ1,appendO,hXh,hX,marks_length]
  have h2O : σ2.val (R 7)=2*(natWord v).length+2*w.length := by
    simp [σ2,copySt,σ1,appendO,hOC,hO,marks_length]
  have e3:=emitC_spec cap X (R 7) false σ2 h2X (by rw [h2O,hNW];omega)
  let σ3:=appendO σ2 X (R 7) [false]
  have e4:=wrewind_spec cap IN C (2*w.length) σ3
    (by simp [σ3,σ2,copySt,σ1,appendO,hOC.symm,hC])
    (by simp [σ3,σ2,copySt,σ1,appendO,hOC.symm,hC];omega)
  let σ4:=(σ3.setv C 0).seth IN (σ3.sh IN-2*w.length)
  have e5:=wrewind_spec cap X (R 7) (2*(natWord v).length+2*w.length+1) σ4
    (by simp [σ4,σ3,appendO,hOC,h2O])
    (by simp [σ4,σ3,appendO,hOC,h2O,hNW];omega)
  refine (WXExec.seq (WXExec.wm e1) (WXExec.seq e2 (WXExec.seq (WXExec.wm e3)
    (WXExec.seq (WXExec.wm e4) (WXExec.wm e5))))).cast cap ?_ ?_
  · apply WState.eq
    · funext i
      by_cases hiX : i=X
      · subst hiX
        simp [σ4,σ3,σ2,σ1,appendO,copySt,hIX.symm,hXh,marks_length]
      · by_cases hiIN : i=IN
        · subst hiIN
          simp [σ4,σ3,σ2,σ1,appendO,copySt,hIX,hINh]
        · simp [σ4,σ3,σ2,σ1,appendO,copySt,hiX,hiIN]
    · funext i
      by_cases hiX : i=X
      · subst hiX
        simp [σ4,σ3,σ2,σ1,appendO,copySt,hX,Codec.frame_eq_marks,NearCubicWires.RepairOrdinary.Streaming.marks_append,List.append_assoc]
      · simp [σ4,σ3,σ2,σ1,appendO,copySt,hiX]
    · funext i
      by_cases hiC : i=C
      · subst hiC
        simp [σ4,σ3,σ2,σ1,appendO,copySt,hOC.symm,hC]
      · by_cases hiO : i=R 7
        · subst hiO
          simp [σ4,σ3,σ2,σ1,appendO,copySt,hOC,hO]
        · simp [σ4,σ3,σ2,σ1,appendO,copySt,hiC,hiO]
    · rfl
  · have hnb : natBitLength v≤v+1 := by
      unfold natBitLength
      have hh:=Nat.log_lt_self 2 (show v+1≠0 by omega)
      have hm:=Nat.log_mono_right (show v≤v+1 by omega) (b:=2)
      omega
    have hm:=Nat.mul_le_mul_right (100*v+200) (show natBitLength v+10≤v+11 by omega)
    unfold writeIndexedCost
    rw [hNW]
    nlinarith

end NearQuarticWires.StagePrint
