import Proof.Quartic.StageNativeMiddleMap.Format
import Proof.Quartic.StageNativeMiddleMap.State
import Proof.Quartic.StageNativeMiddleMap.Transport

set_option autoImplicit false

namespace NearQuarticWires.StageNativeMiddleMap

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close NearCubicGates.Close.WordPrograms

def formatSlots (p : Program) : Fin 4↪Fin (p.tapeCount+20) where
  toFun:=![external p 2,external p 18,external p 4,final p]
  inj':=by
    intro i j h
    fin_cases i <;> fin_cases j <;>
      simp [Fin.ext_iff,external,final] at *

/-- `lem:print`, paper/paper.tex: final
record emission reads the genuinely retained metadata and actual
callee reply; exact fresh output survives read-equivalent work tapes. -/
theorem emit_exec (p : Program) (cap q count : ℕ) (input output : List Bool)
    (a : WState (p.tapeCount+19) 32)
    (hs : SimW (ready p cap q input output count) a) (ho : a.st (final p)=[])
    (hc : 4*((natWord q).length+(frame output).length+(natWord count).length)+100 ≤ cap) :
    ∃ b,WExec cap (formatProgram (formatSlots p) (7 : Fin 32) 8 9) a b
      (1000*((natWord q).length+(frame output).length+(natWord count).length+1)) ∧
      b.st (final p)=frame (StagePrint.NativeMiddle.word q output count) := by
  let ideal:=ready p cap q input output count
  have hf:=ready_fields p cap q input output count
  have hOf : ideal.st (final p)=[] := hf.2.2.2.2.1
  have ee:=format_spec cap (formatSlots p) (7 : Fin 32) 8 9
    (by decide) (by decide) (by decide) q count output ideal hf.1 hf.2.2.1 hf.2.1
    (fun i=>hf.2.2.2.2.2.1 _)
    (by
      change ideal.sh (final p)=(ideal.st (final p)).length
      rw [hf.2.2.2.2.2.1,hOf]
      rfl)
    (hf.2.2.2.2.2.2 8) (hf.2.2.2.2.2.2 9)
    (by rw [hf.2.2.2.2.2.2];simpa only [Nat.zero_add] using hc)
  obtain ⟨b,eb,hb,hout⟩:=wexec_sim_exact ee (final p) a hs (hOf.trans ho.symm)
  refine ⟨b,eb,hout.symm.trans ?_⟩
  change (appendO ideal (final p) (7 : Fin 32)
    (frame (StagePrint.NativeMiddle.word q output count))).st (final p)=_
  simp only [appendO_st,Function.update_self,hOf,List.nil_append]

end NearQuarticWires.StageNativeMiddleMap
