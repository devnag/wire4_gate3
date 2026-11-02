import Proof.Quartic.StageCarrierEnvelope.ModulusField

set_option autoImplicit false

namespace NearQuarticWires.StageCarrierEnvelope

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.CopyNat
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicGates.Close.CounterAsm NearCubicGates.Close.Recovery.HTParts

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: retain the
original ordinary source frame inside its one actual envelope field. -/
def copyCarrierField (src out : Fin (ns+1)) (OP SC : Fin nr) : WM ns nr :=
  .seq (frameCopy src SC (emitQuad out OP)) (emitPair out OP false)

/-- `lem:print` and `prop:time`, paper/paper.tex: the complete original source is copied once, with both
marker layers and every actual source-head advance included. -/
theorem copyCarrierField_run (cap : ℕ) (src out : Fin (ns+1)) (OP SC : Fin nr)
    (hso : src≠out) (hOS : OP≠SC) (bits pre rest : List Bool) (a : WState ns nr)
    (hsource : a.st src=pre++frame bits++rest) (hhead : a.sh src=pre.length)
    (hout : a.sh out=(a.st out).length)
    (hcap : a.val OP+4*(frame bits).length+2≤cap)
    (hsc : a.val SC+(frame bits).length≤cap) :
    WExec cap (copyCarrierField src out OP SC) a
      (appendO (adv src out OP SC a ((frame bits).flatMap quad) (frame bits).length)
        out OP [true,false]) (89*(frame bits).length+16) := by
  have ec:=frameCopy_spec cap hso hOS (emits_quad cap out OP)
    (d:=4) (by intro bit;rfl) bits pre rest a hsource hhead hout (by omega) (by omega)
  let b:=adv src out OP SC a ((frame bits).flatMap quad) (frame bits).length
  have hlen : ((frame bits).flatMap quad).length=4*(frame bits).length := by
    induction frame bits with
    | nil=>rfl
    | cons bit tail ih=>simp only [List.flatMap_cons,List.length_append,quad,List.length_cons,List.length_nil,ih];omega
  have ee:=emitPair_spec cap out OP false b
    (by rw [adv_sh_dst hso,adv_st_dst,hout,List.length_append])
    (by rw [adv_val_OP hOS,hlen];omega)
  exact (ec.seq ee).mono (by omega)

/-- `lem:print`, paper/paper.tex: the actual
binary column-count reply is copied with its envelope marker layer. -/
def copyColumnField (src out : Fin (ns+1)) (OP SC : Fin nr) : WM ns nr :=
  frameCopy src SC (emitPair out OP)

/-- `lem:print` and `prop:time`, paper/paper.tex: the real finite reply frame is consumed bitwise,
without iterating through the numerical column count. -/
theorem copyColumnField_run (cap : ℕ) (src out : Fin (ns+1)) (OP SC : Fin nr)
    (hso : src≠out) (hOS : OP≠SC) (bits pre rest : List Bool) (a : WState ns nr)
    (hsource : a.st src=pre++frame bits++rest) (hhead : a.sh src=pre.length)
    (hout : a.sh out=(a.st out).length)
    (hcap : a.val OP+2*(frame bits).length≤cap)
    (hsc : a.val SC+(frame bits).length≤cap) :
    WExec cap (copyColumnField src out OP SC) a
      (adv src out OP SC a (marks (frame bits)) (frame bits).length)
      (55*(frame bits).length) := by
  have ec:=frameCopy_spec cap hso hOS (NearCubicGates.Close.Recovery.HTParts.emits_pair (cap:=cap) (dst:=out) (OP:=OP))
    (d:=2) (by intro bit;rfl) bits pre rest a hsource hhead hout hcap (by omega)
  simpa only [copyColumnField,marks,Nat.mul_comm] using ec

/-- `lem:print`, paper/paper.tex: the eight
unused envelope fields and the ordinary outer delimiter are literal. -/
def sealEnvelope (out : Fin (ns+1)) (OP : Fin nr) : WM ns nr :=
  .seq (emitWordM out OP (List.replicate 8 false)) (emitC out OP false)

/-- `lem:print` and `prop:time`, paper/paper.tex: all remaining empty fields and the final outer marker
are physically written and included in the source clock. -/
theorem sealEnvelope_run (cap : ℕ) (out : Fin (ns+1)) (OP : Fin nr)
    (a : WState ns nr) (hout : a.sh out=(a.st out).length)
    (hcap : a.val OP+17≤cap) :
    WExec cap (sealEnvelope out OP) a
      (appendO (appendO a out OP (marks (List.replicate 8 false))) out OP [false]) 136 := by
  have ee:=emitWordM_spec cap out OP (List.replicate 8 false) a hout (by simp only [List.length_replicate];omega)
  let b:=appendO a out OP (marks (List.replicate 8 false))
  have eb:=emitC_spec cap out OP false b
    (by simp [b,appendO,hout,List.length_append])
    (by simp [b,appendO,Streaming.marks_length];omega)
  exact (ee.seq eb).mono (by simp only [List.length_replicate];omega)

end NearQuarticWires.StageCarrierEnvelope
