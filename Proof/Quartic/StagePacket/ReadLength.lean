import Proof.Quartic.StagePacket.LengthRegisters

set_option autoImplicit false

namespace NearQuarticWires.StagePacket

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: decode only
the actual payload byte count, then account for its source codec
using the binary length obtained by real halving instructions. -/
def readPayloadLength (src : Fin (ns+1)) (R : Fin 16 ↪ Fin nr) : WM ns nr :=
  .seq (readNatM false src (R 6) (R 7) (R 5) (R 8) (R 9))
    (.seq (bitLenM (lengthRegisters R))
      (.seq (addTo (R 10) (R 2) (R 11))
        (.seq (addTo (R 10) (R 2) (R 11)) (.inc (R 2)))))

/-- `prop:time`, paper/paper.tex: the actual
length reader's complete clock includes decoding, binary length,
both measured-counter additions and their final increment. -/
def payloadLengthCost (value : ℕ) : ℕ :=
  (natBitLength value+2)*(40*2^natBitLength value+40)+60*value+36*natBitLength value+73

/-- `lem:print`, paper/paper.tex: source,
payload length and measured consumption are the actual final state
of the length-reader instructions, with all other fields retained. -/
def payloadLengthState (src : Fin (ns+1)) (R : Fin 16 ↪ Fin nr)
    (a : WState ns nr) (position value : ℕ) : WState ns nr :=
  (((a.seth src (position+(natWord value).length)).setv (R 5) value).setv (R 10)
    (natBitLength value)).setv (R 2) (a.val (R 2)+(natWord value).length)

/-- `lem:print` and `prop:time`, paper/paper.tex: the payload-length value is decoded from its literal
fourth source field, with no supplied length register and no scan of
the arbitrary following bytes. Only this consumed-length value is
decoded numerically; original indices and hints remain encoded bits. -/
theorem readPayloadLength_spec (cap : ℕ) (src : Fin (ns+1)) (R : Fin 16 ↪ Fin nr)
    (value : ℕ) (pre suffix : List Bool) (a : WState ns nr)
    (hsource : a.st src=pre++natWord value++suffix) (hhead : a.sh src=pre.length)
    (hzero : ∀ j : Fin 16,j.val∈[5,6,7,8,9,10,11,12,13]→a.val (R j)=0)
    (hdecode : 2^(natBitLength value+1)≤cap) (hsmall : value+2≤cap)
    (hcounter : a.val (R 2)+(natWord value).length≤cap) :
    WExec cap (readPayloadLength src R) a (payloadLengthState src R a pre.length value)
      (payloadLengthCost value) := by
  have h5 : a.val (R 5)=0 := hzero 5 (by decide)
  have eRead:=readNatM_spec cap false src (R 6) (R 7) (R 5) (R 8) (R 9)
    (register_ne R (by decide)) (register_ne R (by decide)) (register_ne R (by decide))
    (register_ne R (by decide)) (register_ne R (by decide)) (register_ne R (by decide))
    (register_ne R (by decide)) (register_ne R (by decide)) (register_ne R (by decide))
    (register_ne R (by decide)) value pre suffix a (by simpa only [NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.enc, Bool.false_eq_true, ite_false] using hsource)
    hhead (hzero 6 (by decide)) (hzero 7 (by decide)) (hzero 8 (by decide)) (hzero 9 (by decide))
    (by rw [h5,Nat.zero_add];exact hdecode)
  simp only [stp, Bool.false_eq_true, ite_false, Nat.one_mul,h5,Nat.zero_add] at eRead
  let b:=(a.seth src (pre.length+(natWord value).length)).setv (R 5) value
  have hb (j : Fin 16) (hj : j≠5) : b.val (R j)=a.val (R j) := by
    simp only [b,WState.setv_val,Function.update_of_ne (register_ne R hj),WState.seth_val]
  have hb5 : b.val (R 5)=value := by simp [b]
  have eBits:=bitLenM_spec cap (lengthRegisters R) b
    (by change b.val (R 6)=0;rw [hb 6 (by decide)];exact hzero 6 (by decide))
    (by change b.val (R 7)=0;rw [hb 7 (by decide)];exact hzero 7 (by decide))
    (by change b.val (R 8)=0;rw [hb 8 (by decide)];exact hzero 8 (by decide))
    (by change b.val (R 10)=0;rw [hb 10 (by decide)];exact hzero 10 (by decide))
    (by change b.val (R 9)=0;rw [hb 9 (by decide)];exact hzero 9 (by decide))
    (by change b.val (R 5)+2≤cap;rw [hb5];exact hsmall)
  change WExec cap (bitLenM (lengthRegisters R)) b (b.setv (R 10) (natBitLength (b.val (R 5))))
    (60*b.val (R 5)+60) at eBits
  rw [hb5] at eBits
  let c:=b.setv (R 10) (natBitLength value)
  have hc10 : c.val (R 10)=natBitLength value := by simp [c]
  have hc2 : c.val (R 2)=a.val (R 2) := by
    rw [WState.setv_val,Function.update_of_ne (register_ne R (by decide)),hb 2 (by decide)]
  have hc11 : c.val (R 11)=0 := by
    rw [WState.setv_val,Function.update_of_ne (register_ne R (by decide)),hb 11 (by decide)]
    exact hzero 11 (by decide)
  have hbitscap : natBitLength value≤cap := by rw [NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_length] at hcounter;omega
  have eAdd1:=addTo_spec cap (R 10) (R 2) (R 11)
    (register_ne R (by decide)) (register_ne R (by decide)) (register_ne R (by decide))
    c hc11 (by rw [hc10];exact hbitscap) (by rw [hc2,hc10];rw [NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_length] at hcounter;omega)
  let d:=c.setv (R 2) (c.val (R 2)+c.val (R 10))
  have hd10 : d.val (R 10)=natBitLength value := by
    rw [WState.setv_val,Function.update_of_ne (register_ne R (by decide)),hc10]
  have hd2 : d.val (R 2)=a.val (R 2)+natBitLength value := by simp [d,hc2,hc10]
  have hd11 : d.val (R 11)=0 := by
    rw [WState.setv_val,Function.update_of_ne (register_ne R (by decide)),hc11]
  have eAdd2:=addTo_spec cap (R 10) (R 2) (R 11)
    (register_ne R (by decide)) (register_ne R (by decide)) (register_ne R (by decide))
    d hd11 (by rw [hd10];exact hbitscap)
    (by rw [hd2,hd10];rw [NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_length] at hcounter;omega)
  let e:=d.setv (R 2) (d.val (R 2)+d.val (R 10))
  have he2 : e.val (R 2)=a.val (R 2)+2*natBitLength value := by simp [e,hd2,hd10];omega
  have eInc:=WExec.inc (cap:=cap) (R 2) e (by
    rw [he2]
    rw [NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_length] at hcounter
    omega)
  refine WExec.cast cap (WExec.seq eRead (WExec.seq eBits (WExec.seq eAdd1 (WExec.seq eAdd2 eInc)))) ?_ ?_
  · rw [he2]
    dsimp only [e,d]
    rw [wsetv_setv,wsetv_setv]
    change c.setv (R 2) (a.val (R 2)+2*natBitLength value+1)=
      c.setv (R 2) (a.val (R 2)+(natWord value).length)
    rw [NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_length]
    congr 1
  · rw [hc10,hd10]
    unfold payloadLengthCost
    omega

end NearQuarticWires.StagePacket
