import Proof.Quartic.StageCarrierEnvelope.Quad

set_option autoImplicit false

namespace NearQuarticWires.StageCarrierEnvelope

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close.CounterAsm NearCubicGates.Close.Recovery.HTParts

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: the actual
first modulus codec is copied bitwise into its nested envelope field;
only its unary bit-length prefix is counted, never its numerical value. -/
def copyModulusField (src out : Fin (ns+1)) (OP SC K : Fin nr) : WM ns nr :=
  .seq (natCopy src SC K (emitQuad out OP)) (emitPair out OP false)

/-- `lem:print` and `prop:time`, paper/paper.tex: every copied modulus bit, delimiter and actual source
advance is charged, while an arbitrary remaining carrier suffix is unread. -/
theorem copyModulusField_run (cap : ℕ) (src out : Fin (ns+1)) (OP SC K : Fin nr)
    (hso : src≠out) (hOS : OP≠SC) (hKO : K≠OP) (hKS : K≠SC)
    (q : ℕ) (pre rest : List Bool) (a : WState ns nr)
    (hsource : a.st src=pre++natWord q++rest) (hhead : a.sh src=pre.length)
    (hout : a.sh out=(a.st out).length) (hK : a.val K=0)
    (hcap : a.val OP+4*(natWord q).length+2≤cap)
    (hsc : a.val SC+(natWord q).length≤cap) :
    WExec cap (copyModulusField src out OP SC K) a
      (appendO (adv src out OP SC a ((natWord q).flatMap quad) (natWord q).length) out OP [true,false])
      (45*(natWord q).length+16) := by
  have eqcopy:=natCopy_spec cap hso hOS hKO hKS (emits_quad cap out OP)
    (d:=4) (by intro bit;rfl) q pre rest a hsource hhead hout hK (by omega) (by omega) (by omega)
  let b:=adv src out OP SC a ((natWord q).flatMap quad) (natWord q).length
  have hlen : ((natWord q).flatMap quad).length=4*(natWord q).length := by
    induction natWord q with
    | nil=>rfl
    | cons bit bits ih=>simp only [List.flatMap_cons,List.length_append,quad,List.length_cons,List.length_nil,ih];omega
  have eend:=emitPair_spec cap out OP false b
    (by rw [adv_sh_dst hso,adv_st_dst,hout,List.length_append])
    (by rw [adv_val_OP hOS,hlen];omega)
  exact (eqcopy.seq eend).mono (by omega)

end NearQuarticWires.StageCarrierEnvelope
