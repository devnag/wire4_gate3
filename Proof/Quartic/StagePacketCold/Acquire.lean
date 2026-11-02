import Proof.Quartic.StageGamma.Unframe
import Proof.Gates.Expand.PolyTabPack
import Proof.Quartic.StagePacket.CopyFields
import Proof.Quartic.StagePacket.ProjectionCodec

set_option autoImplicit false

namespace NearQuarticWires.StagePacketCold

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.FinalPass.Hash4
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close.Expand.PolyTab

/-- `lem:print`, paper/paper.tex: the finite
ordinary packet starts on its actual input frame with fresh workspace. -/
def packetStart (bits : List Bool) : WState 2 6 := idealStart 2 6 bits (fun _=>0)

/-- `lem:print`, paper/paper.tex: physically
unframe once, retain the measured byte count, and rewind the raw copy. -/
def acquirePacket : WM 2 6 :=
  .seq (.whs 0 (StageGamma.unframePair 0 1 0))
    (.seq (wcopyR 0 1 2) (WM.rewind 1 0))

/-- `lem:print`, paper/paper.tex: the acquired
raw tape and its size register arise from actual copy instructions. -/
def acquiredPacket (bits : List Bool) : WState 2 6 :=
  (((packetStart bits).sets 1 bits).seth 0 (2*bits.length)).setv 1 bits.length

/-- `lem:print` and `prop:time`, paper/paper.tex: finite packet entry physically obtains the raw bytes
and their length, without a supplied byte-count register or raw tape. -/
theorem acquirePacket_spec (bits : List Bool) (cap : ℕ) (hcap : 2*bits.length+4≤cap) :
    WExec cap acquirePacket (packetStart bits) (acquiredPacket bits) (50*bits.length+20) := by
  let a:=packetStart bits
  have eUnframe:=StageGamma.unframe_loop cap (0 : Fin 3) 1 (by decide) (0 : Fin 6) [] bits [] a
    (by simp [a,packetStart,idealStart]) rfl rfl (by change 0+bits.length≤cap;omega)
  simp only [List.length_nil,Nat.zero_add] at eUnframe
  let b:=(appendO a 1 0 bits).seth 0 (2*bits.length)
  have hb0 : b.val 0=bits.length := by simp [b,a,packetStart,idealStart]
  have eCopy:=wcopyR_spec cap (0 : Fin 6) 1 2 (by decide) (by decide) (by decide) b
    (by simp [b,a,packetStart,idealStart,appendO])
    (by simp [b,a,packetStart,idealStart,appendO]) (by rw [hb0];omega)
  rw [hb0] at eCopy
  let c:=b.setv 1 bits.length
  have eRewind:=wrewind_spec cap (1 : Fin 3) (0 : Fin 6) bits.length c
    (by simp [c,hb0]) (by simp [c,hb0];omega)
  refine (eUnframe.seq (eCopy.seq eRewind)).cast cap ?_ (by omega)
  apply WState.eq
  · funext stream
    fin_cases stream <;> simp [c,b,a,acquiredPacket,packetStart,idealStart,appendO]
  · funext stream
    fin_cases stream <;> simp [c,b,a,acquiredPacket,packetStart,idealStart,appendO]
  · funext reg
    fin_cases reg <;> simp [c,b,a,acquiredPacket,packetStart,idealStart,appendO]
  · rfl

end NearQuarticWires.StagePacketCold
