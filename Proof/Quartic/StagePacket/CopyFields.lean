import Proof.Quartic.StagePrint.PacketInterface

set_option autoImplicit false

namespace NearQuarticWires.StagePacket

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.CounterAsm NearCubicGates.Close.Recovery.HTParts

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: copy a fixed
number of actual natural fields without decoding their magnitudes. -/
def copyNaturalFields (src : Fin (ns+1)) (SC K : Fin nr) (emit : Bool→WM ns nr) : ℕ→WM ns nr
  | 0=>.skip
  | count+1=>.seq (natCopy src SC K emit) (copyNaturalFields src SC K emit count)

/-- `lem:print` and `prop:time`, paper/paper.tex: the fixed field reader measures its real source
consumption, copies only the encoded prefix, and leaves an arbitrary
following suffix unread, regardless of the scalar values it encodes. -/
theorem copyNaturalFields_spec (cap : ℕ) (src dst : Fin (ns+1)) (OP SC K : Fin nr)
    (hsd : src≠dst) (hOS : OP≠SC) (hKO : K≠OP) (hKS : K≠SC)
    (emit : Bool→WM ns nr) (encoding : Bool→List Bool) (cost width : ℕ)
    (hEmit : Emits cap dst OP encoding emit cost) (hwidth : EmitLen encoding width)
    (fields : List ℕ) (pre suffix : List Bool) (a : WState ns nr)
    (hsource : a.st src=pre++fields.flatMap natWord++suffix) (hhead : a.sh src=pre.length)
    (hout : a.sh dst=(a.st dst).length) (hK : a.val K=0)
    (houtputCap : a.val OP+width*(fields.flatMap natWord).length≤cap)
    (hsourceCap : a.val SC+(fields.flatMap natWord).length≤cap) :
    WExec cap (copyNaturalFields src SC K emit fields.length) a
      (adv src dst OP SC a ((fields.flatMap natWord).flatMap encoding) (fields.flatMap natWord).length)
      ((fields.flatMap natWord).length*(cost+13)+fields.length) := by
  induction fields generalizing pre a with
  | nil =>
      simp only [List.length_nil,List.flatMap_nil,Nat.zero_mul,Nat.zero_add,adv_zero]
      exact WExec.skip a
  | cons value fields ih =>
      have hword : a.st src=pre++natWord value++(fields.flatMap natWord++suffix) := by
        simpa only [List.flatMap_cons,List.append_assoc] using hsource
      have hfront : (natWord value).length≤(natWord value).length+(fields.flatMap natWord).length := by omega
      have eFront:=natCopy_spec cap hsd hOS hKO hKS hEmit hwidth value pre
        (fields.flatMap natWord++suffix) a hword hhead hout hK
        (by simp only [List.flatMap_cons,List.length_append] at houtputCap; nlinarith)
        (by simp only [List.flatMap_cons,List.length_append] at hsourceCap;omega)
        (by simp only [List.flatMap_cons,List.length_append] at hsourceCap;omega)
      let b:=adv src dst OP SC a ((natWord value).flatMap encoding) (natWord value).length
      have hbsource : b.st src=(pre++natWord value)++fields.flatMap natWord++suffix := by
        rw [adv_st_src hsd,hsource]
        simp only [List.flatMap_cons,List.append_assoc]
      have hbhead : b.sh src=(pre++natWord value).length := by
        rw [adv_sh_src,hhead,List.length_append]
      have hbout : b.sh dst=(b.st dst).length := by
        rw [adv_sh_dst hsd,adv_st_dst,hout,List.length_append]
      have hbK : b.val K=0 := by rw [adv_val_other _ _ _ K hKO hKS,hK]
      have emittedFront:=flatMap_emit_le hwidth (natWord value)
      have hbOCap : b.val OP+width*(fields.flatMap natWord).length≤cap := by
        rw [adv_val_OP hOS]
        simp only [List.flatMap_cons,List.length_append] at houtputCap
        nlinarith
      have hbSCap : b.val SC+(fields.flatMap natWord).length≤cap := by
        rw [adv_val_SC]
        simp only [List.flatMap_cons,List.length_append] at hsourceCap
        omega
      have eTail:=ih (pre++natWord value) b hbsource hbhead hbout hbK hbOCap hbSCap
      refine WExec.cast cap (WExec.seq eFront eTail) ?_ ?_
      · rw [adv_adv hsd hOS]
        simp only [List.flatMap_cons,List.flatMap_append,List.length_append]
      · simp only [List.flatMap_cons,List.length_append,List.length_cons]
        nlinarith

end NearQuarticWires.StagePacket
