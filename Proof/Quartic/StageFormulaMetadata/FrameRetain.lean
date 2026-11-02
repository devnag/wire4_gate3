import Proof.Quartic.StageFormulaMetadata.FrameCount

set_option autoImplicit false

namespace NearQuarticWires.StageFormulaMetadata

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open StageLift

/-- `lem:print`, paper/paper.tex: retain the
literal original postfix payload and compute its runtime length. -/
def readCountedFrame (store : Fin MM) : St VV MM :=
  .seq (.op (.rdI t0)) (.loop (.eq t0 v1) (countedFrameBody store))

/-- `prop:time`, paper/paper.tex: the complete
physical frame reader includes its leading marker, every retained
bit and the terminal marker, ending before the following source. -/
theorem readCountedFrame_spec (C : Ctx) (store : Fin MM) (bits rest : List Bool)
    (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip=frame bits++rest)
    (hcursor : a.rc store=(a.ram store).length)
    (hfit : a.env payloadLengthVar+bits.length<2^C.Wd) :
    Hs C (readCountedFrame store) a (10*bits.length+4) (fun b=>
      b.env payloadLengthVar=a.env payloadLengthVar+bits.length ∧
      b.ip=a.ip+(frame bits).length ∧ b.ram store=a.ram store++bits.map Bool.toNat ∧
      b.rc store=a.rc store+bits.length ∧
      (∀ other,other≠store→b.ram other=a.ram other ∧ b.rc other=a.rc other) ∧
      (b.out,b.kin,b.kout,b.kc)=(a.out,a.kin,a.kout,a.kc) ∧
      Cst b ∧ Fr a b [t0,t1,payloadLengthVar]) := by
  unfold readCountedFrame
  refine (Hs.seq (t2:=10*bits.length+2)
    (readInputBit_spec C t0 a (frameFlag bits) (framePayload bits++rest)
      (by simpa only [frame_decompose,List.cons_append] using hin)) fun b hb=>?_).mono
        (by omega) (fun _ h=>h)
  subst b
  let d:={a.set t0 (frameFlag bits).toNat with ip:=a.ip+1}
  have hdc : Cst d := by
    constructor
    · simpa (config:={decide:=true}) [d,DS.set] using hc.z
    · simpa (config:={decide:=true}) [d,DS.set] using hc.one
    · simpa (config:={decide:=true}) [d,DS.set] using hc.two
  have hdinput : C.inp.drop d.ip=framePayload bits++rest := by
    change C.inp.drop (a.ip+1)=_
    rw [←List.drop_drop,hin,frame_decompose]
    rfl
  have hdl : d.env payloadLengthVar=a.env payloadLengthVar := by
    simp (config:={decide:=true}) [d,DS.set]
  refine (countedFrameLoop_spec C store bits rest d hdc (by simp [d]) hdinput hcursor
    (by rwa [hdl])).mono le_rfl ?_
  rintro b ⟨_hz,hbl,hbi,hbr,hbrc,hbo,hbrest,hbc,hbf⟩
  refine ⟨by simpa only [hdl] using hbl,?_,hbr,hbrc,hbo,hbrest,hbc,?_⟩
  · change b.ip=a.ip+1+2*bits.length at hbi
    rw [frame_length]
    omega
  · exact (Fr.set a _ (by simp)).trans hbf

end NearQuarticWires.StageFormulaMetadata
