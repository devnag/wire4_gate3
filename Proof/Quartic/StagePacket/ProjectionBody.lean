import Proof.Quartic.StagePacket.ProjectionCodec

set_option autoImplicit false

namespace NearQuarticWires.StagePacket

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close.CounterAsm NearCubicGates.Close.Recovery.HTParts
open StagePrint.PacketInterface NearCubicGates.Close.Interfaces.Formats

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: the actual
Formula reader copies both binary header codecs and the measured
number of original signed postfix bytes, then seals their frame. -/
def projectBody (src dst : Fin (ns+1)) (R : Fin 16 ↪ Fin nr) : WM ns nr :=
  .seq (copyNaturalFields src (R 2) (R 4) (fun bit=>emitPair dst (R 0) bit) 2)
    (.seq (cntLoop src (R 2) (R 5) (fun bit=>emitPair dst (R 0) bit))
      (emitC dst (R 0) false))

/-- `lem:print`, paper/paper.tex: Formula's
literal bytes are copied unchanged; the payload counter is consumed. -/
def projectionBodyState (src dst : Fin (ns+1)) (R : Fin 16 ↪ Fin nr)
    (a : WState ns nr) (r : ExactProjectionRequest) : WState ns nr :=
  appendO ((adv src dst (R 0) (R 2) a ((formulaWord r.formula).flatMap fun bit=>[true,bit])
    (formulaWord r.formula).length).setv (R 5) 0) dst (R 0) [false]

/-- `prop:time`, paper/paper.tex: the signed
Formula copy charges its actual header and raw payload bytes. -/
def projectionBodyCost (r : ExactProjectionRequest) : ℕ :=
  28*([r.formula.1,(toks r.formula.2).length].flatMap natWord).length+26*r.payload.length+12

/-- `lem:print` and `prop:time`, paper/paper.tex: physical Formula projection preserves every signed
constant bit and stops before an arbitrary following source suffix. -/
theorem projectBody_spec (cap : ℕ) (src dst : Fin (ns+1)) (R : Fin 16 ↪ Fin nr)
    (hsd : src≠dst) (r : ExactProjectionRequest) (pre suffix : List Bool) (a : WState ns nr)
    (hsource : a.st src=pre++formulaWord r.formula++suffix) (hhead : a.sh src=pre.length)
    (hout : a.sh dst=(a.st dst).length) (h4 : a.val (R 4)=0)
    (h5 : a.val (R 5)=r.payload.length)
    (houtput : a.val (R 0)+2*(formulaWord r.formula).length+1≤cap)
    (hinput : a.val (R 2)+(formulaWord r.formula).length≤cap) :
    WExec cap (projectBody src dst R) a (projectionBodyState src dst R a r)
      (projectionBodyCost r) := by
  have h02 : R 0≠R 2 := register_ne R (by decide)
  have h40 : R 4≠R 0 := register_ne R (by decide)
  have h42 : R 4≠R 2 := register_ne R (by decide)
  have h50 : R 5≠R 0 := register_ne R (by decide)
  have h52 : R 5≠R 2 := register_ne R (by decide)
  let fields:=[r.formula.1,(toks r.formula.2).length]
  let header:=fields.flatMap natWord
  have hword : formulaWord r.formula=header++r.payload := projection_formula_word r
  have hm : (formulaWord r.formula).length=header.length+r.payload.length := by
    rw [hword,List.length_append]
  have eHeader:=copyNaturalFields_spec cap src dst (R 0) (R 2) (R 4) hsd h02 h40 h42
    (fun bit=>emitPair dst (R 0) bit) (fun bit=>[true,bit]) 15 2
    (emits_pair (cap:=cap)) (by intro bit;simp) fields pre (r.payload++suffix) a
    (by simpa only [hword,List.append_assoc] using hsource) hhead hout h4
    (by change a.val (R 0)+2*header.length≤cap;omega)
    (by change a.val (R 2)+header.length≤cap;omega)
  let b:=adv src dst (R 0) (R 2) a (header.flatMap fun bit=>[true,bit]) header.length
  have hbout : b.sh dst=(b.st dst).length := by
    rw [adv_sh_dst hsd,adv_st_dst,hout,List.length_append]
  have hb5 : b.val (R 5)=r.payload.length := by rw [adv_val_other _ _ _ _ h50 h52,h5]
  have ePayload:=cntLoop_spec (cap:=cap) hsd h02 h50 h52 (emits_pair (cap:=cap)) suffix
    r.payload (pre++header) b
    (by rw [adv_st_src hsd,hsource,hword];simp only [List.append_assoc])
    (by rw [adv_sh_src,hhead,List.length_append]) hbout hb5 (by omega)
    (by rw [adv_val_OP h02,paired_length,paired_length];omega)
    (by rw [adv_val_SC];omega)
  let c:=((adv src dst (R 0) (R 2) b (r.payload.flatMap fun bit=>[true,bit]) r.payload.length).setv (R 5) 0)
  have hcout : c.sh dst=(c.st dst).length := by
    simp only [c,WState.setv_sh,WState.setv_st,adv_sh_dst hsd,adv_st_dst,hbout,List.length_append]
  have eMark:=NearCubicGates.Close.Codec.emitBit_spec cap dst (R 0) false c hcout (by
    simp only [c,WState.setv_val,Function.update_of_ne h50.symm,adv_val_OP h02,paired_length,b]
    omega)
  refine WExec.cast cap (WExec.seq eHeader (WExec.seq ePayload eMark)) ?_ ?_
  · dsimp only [c,b,projectionBodyState]
    rw [adv_adv hsd h02]
    rw [hword,List.flatMap_append,List.length_append]
  · dsimp only [projectionBodyCost,fields,header]
    simp only [List.length_cons,List.length_nil]
    omega

end NearQuarticWires.StagePacket
