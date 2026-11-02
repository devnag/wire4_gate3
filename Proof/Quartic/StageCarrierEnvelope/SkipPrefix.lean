import Proof.Quartic.StageCarrierEnvelope.Acquire
import Proof.Quartic.StagePacket.CopyFields
import Proof.Wire_3_5.PrimAsmParseNat

set_option autoImplicit false

namespace NearQuarticWires.StageCarrierEnvelope

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicGates.Close.CounterAsm NearCubicGates.Close.Recovery.HTParts

variable {ns : ℕ}

/-- `lem:print`, paper/paper.tex: decode only
the finite preparation length, pass its actual bytes, then skip the three
following binary codecs without decoding count, ordinal or degree values. -/
def skipCarrierPrefix (src : Fin (ns+1)) : WM ns 16 :=
  .seq (readNatM false src 3 4 5 6 7)
    (.seq (cntLoop src 0 5 (fun _=>WM.skip))
      (StagePacket.copyNaturalFields src 0 2 (fun _=>WM.skip) 3))

/-- `lem:print`, paper/paper.tex: the first
modulus lies at the exact physically consumed prefix cursor; the saved
whole-carrier length register is preserved. -/
def firstModulusState (src : Fin (ns+1)) (a : WState ns 16)
    (prep : List Bool) (fields : List ℕ) : WState ns 16 :=
  (a.seth src ((natWord prep.length).length+prep.length+(fields.flatMap natWord).length)).setv 0
    (prep.length+(fields.flatMap natWord).length)

/-- `lem:print` and `prop:time`, paper/paper.tex: the genuine first-entry modulus cursor is obtained
by actual finite-prefix reads, preserving every following source byte
and never iterating through a count, degree or modulus magnitude. -/
theorem skipCarrierPrefix_run (cap : ℕ) (src dst : Fin (ns+1)) (hsd : src≠dst)
    (prep : List Bool) (fields : List ℕ) (hfields : fields.length=3) (rest : List Bool)
    (a : WState ns 16)
    (hsource : a.st src=natWord prep.length++prep++fields.flatMap natWord++rest)
    (hhead : a.sh src=0) (hout : a.sh dst=(a.st dst).length)
    (hz : ∀i : Fin 16,i≠8→a.val i=0)
    (hcap : 2^(natBitLength prep.length+1)+prep.length+(fields.flatMap natWord).length+10≤cap) :
    WExec cap (skipCarrierPrefix src) a (firstModulusState src a prep fields)
      ((natBitLength prep.length+2)*(40*2^natBitLength prep.length+40)+
        100*(prep.length+(fields.flatMap natWord).length+1)) := by
  have hpow : 0≤2^natBitLength prep.length:=Nat.zero_le _
  have hPcap : prep.length≤cap := by omega
  have hFcap : prep.length+(fields.flatMap natWord).length≤cap := by omega
  have er:=readNatM_spec cap false src (3 : Fin 16) 4 5 6 7
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    prep.length [] (prep++fields.flatMap natWord++rest) a
    (by simpa only [NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.enc,Bool.false_eq_true,ite_false,List.nil_append,List.append_assoc] using hsource)
    (by simpa using hhead) (hz 3 (by decide)) (hz 4 (by decide))
    (hz 6 (by decide)) (hz 7 (by decide)) (by rw [hz 5 (by decide)];omega)
  simp only [List.length_nil,Nat.zero_add,stp,Bool.false_eq_true,ite_false,one_mul,hz 5 (by decide)] at er
  let b:=(a.seth src (natWord prep.length).length).setv 5 prep.length
  have hnil (bits : List Bool) : bits.flatMap (fun _=>([] : List Bool))=[] := by simp
  have eb:=cntLoop_spec (cap:=cap) (src:=src) (dst:=dst) (OP:=(1 : Fin 16)) (SC:=0)
    hsd (by decide) (K:=5) (by decide) (by decide) (emits_none (cap:=cap))
    (fields.flatMap natWord++rest) prep (natWord prep.length) b
    (by simp [b,hsource,List.append_assoc]) (by simp [b])
    (by simp [b,hout,Function.update_of_ne hsd.symm]) (by simp [b]) hPcap
    (by simp [b,hz 1 (by decide),hnil]) (by simp only [b,WState.setv_val,Function.update_of_ne (by decide : (0 : Fin 16)≠5),WState.seth_val,hz 0 (by decide),Nat.zero_add];exact Nat.lt_succ_of_le hPcap)
  rw [hnil] at eb
  let c:=(adv src dst (1 : Fin 16) 0 b [] prep.length).setv 5 0
  have ec:=StagePacket.copyNaturalFields_spec cap src dst (1 : Fin 16) 0 2 hsd
    (by decide) (by decide) (by decide) (fun _=>WM.skip) (fun _=>[]) 0 0
    (emits_none (cap:=cap)) (by intro bit;rfl) fields (natWord prep.length++prep) rest c
    (by simp [c,b,adv,appendO,hsource,List.append_assoc])
    (by simp [c,b,adv,appendO_nil,List.length_append])
    (by simp [c,b,adv,appendO_nil,Function.update_of_ne hsd.symm,hout]) (by simp [c,b,adv,appendO_nil,hz 2 (by decide)])
    (by simp [c,b,adv,appendO_nil,hz 1 (by decide)])
    (by simp only [c,b,adv,appendO_nil,WState.setv_val,WState.seth_val,Function.update_of_ne (by decide : (0 : Fin 16)≠5),Function.update_self,hz 0 (by decide),Nat.zero_add];exact hFcap)
  rw [hfields] at ec
  rw [hnil] at ec
  refine (er.seq (eb.seq ec)).cast cap ?_ (by omega)
  apply WState.eq
  · funext stream
    by_cases hs : stream=src
    · subst stream
      simp [c,b,firstModulusState,adv,appendO_nil]
    · simp [c,b,firstModulusState,adv,appendO_nil,hs]
  · funext stream
    simp [c,b,firstModulusState,adv,appendO_nil]
  · funext reg
    by_cases h0 : reg=0
    · subst reg
      simp [c,b,firstModulusState,adv,appendO_nil,hz 0 (by decide)]
    · by_cases h5 : reg=5
      · subst reg
        simp [c,b,firstModulusState,adv,appendO_nil,hz 5 (by decide)]
      · simp [c,b,firstModulusState,adv,appendO_nil,h0,h5]
  · rfl

end NearQuarticWires.StageCarrierEnvelope
