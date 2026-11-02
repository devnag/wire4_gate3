import Proof.Quartic.StagePacket.CopyFields
import Proof.Wire_3_5.PrimAsmCopyNat

set_option autoImplicit false

namespace NearQuarticWires.StageCarrierEnvelope

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.CopyNat
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicGates.Close.Recovery.HTParts

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: every
metadata bit receives its real field-frame and outer-envelope markers. -/
def quad (bit : Bool) : List Bool := [true,true,true,bit]

def emitQuad (out : Fin (ns+1)) (OP : Fin nr) (bit : Bool) : WM ns nr :=
  emitWordM out OP [true,bit]

/-- `lem:print` and `prop:time`, paper/paper.tex: all four actual output bits and their counted head
movements are paid for each nested field bit. -/
theorem emits_quad (cap : ℕ) (out : Fin (ns+1)) (OP : Fin nr) :
    Emits cap out OP quad (emitQuad out OP) 32 := by
  intro bit a hout hcap
  simpa [emitQuad,quad,marks] using
    emitWordM_spec cap out OP [true,bit] a hout (by simpa only [quad,List.length_cons,List.length_nil] using hcap)

/-- `lem:print`, paper/paper.tex: two actual
marker layers preserve every signed source and metadata payload bit. -/
theorem flatMap_quad (bits : List Bool) : bits.flatMap quad=marks (marks bits) := by
  induction bits with
  | nil=>rfl
  | cons bit bits ih=>simpa only [quad,marks,List.flatMap_cons,List.flatMap_nil,List.append_nil,
      List.cons_append,List.singleton_append,List.nil_append] using congrArg (fun tail=>true::true::true::bit::tail) ih

/-- `lem:print`, paper/paper.tex: the actual
field delimiter receives the same outer marker layer as payload bits. -/
theorem quad_frame (bits : List Bool) : bits.flatMap quad++[true,false]=marks (frame bits) := by
  rw [flatMap_quad,NearCubicGates.Close.Codec.frame_eq_marks]
  simp only [marks,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]

end NearQuarticWires.StageCarrierEnvelope
