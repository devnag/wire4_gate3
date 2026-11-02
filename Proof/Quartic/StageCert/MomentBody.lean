import Proof.Quartic.StageCert.MomentPacket
import Proof.Quartic.StageCert.MomentFrontend

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells

/-- `lem:print`, paper/paper.tex: read the actual
finite source and generated structural suffix, then emit the complete
original exact-CERT packet, including its signed postfix payload. -/
def momentBody : St VV MM := .seq readMomentSource emitMomentPacket

/-- `lem:print` and `prop:time`, paper/paper.tex: actual cold original source bytes and the actual
frontend output suffice for the full signed packet source. -/
theorem momentBody_run {B1 B2 : ℕ} (C : Ctx) (r : MomentRequest B1 B2)
    (rest : List Bool) (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip=r.flaggedWord++rest) (hwidth : r.bodyCapacity≤C.Wd)
    (hempty : ∀store,a.ram store=[] ∧ a.rc store=0) (hKC : a.kc≤a.kout.length) :
    Hs C momentBody a (r.readSteps+r.packetSteps+1) (fun z=>
      z.out=a.out++r.packet.word ∧ z.ip=a.ip+r.flaggedWord.length ∧ Cst z) := by
  have hcap := r.body_capacity C.Wd hwidth
  have hRC : ∀store,a.rc store≤(a.ram store).length := by
    intro store
    rw [(hempty store).1,(hempty store).2]
    rfl
  unfold momentBody
  apply Hx.hs
  refine Hs.then ((readMomentSource_run C r
    (structuralFlagList r (momentFlagEdges r.test)++rest) a hc
    (by simpa only [MomentRequest.flaggedWord,List.append_assoc] using hin)
    hcap.source hempty).rc_le hRC hKC)
    (fun b ⟨⟨bd,bi,bs,bc⟩,bRC,bKC⟩ n1 hn1=>?_)
  have bin : C.inp.drop b.ip=structuralFlagList r (momentFlagEdges r.test)++rest := by
    rw [bi,←List.drop_drop,hin]
    simp only [MomentRequest.flaggedWord,List.append_assoc,List.drop_left]
  refine Hs.last (emitMomentPacket_run C r rest b bc bd hwidth bRC bKC bin)
    (fun z ⟨zo,zi,zc⟩ n2 hn2=>?_)
  refine ⟨⟨?_,?_,zc⟩,by omega⟩
  · rw [zo,show b.out=a.out from congrArg (fun q=>q.1) bs]
  · rw [zi,bi]
    simp only [MomentRequest.flaggedWord,List.length_append,structuralFlagList,List.length_map]
    omega

end NearQuarticWires.StageCert.Tokens
