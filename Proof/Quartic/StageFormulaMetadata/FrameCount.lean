import Proof.Quartic.StageLift.FrameLoop

set_option autoImplicit false

namespace NearQuarticWires.StageFormulaMetadata

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open StageLift

/-- `lem:print`, paper/paper.tex: the original
postfix byte count is physically incremented while retaining its frame. -/
def payloadLengthVar : Fin VV := 106

/-- `lem:print`, paper/paper.tex: one framed
payload bit is read, retained and counted by actual instructions. -/
def countedFrameBody (store : Fin MM) : St VV MM :=
  .seq (frameReadBody store) (.op (.inc payloadLengthVar))

/-- `prop:time`, paper/paper.tex: framed source
retention computes its own byte count and preserves the following
source suffix without an externally supplied payload length. -/
theorem countedFrameLoop_spec (C : Ctx) (store : Fin MM) (bits rest : List Bool)
    (a : DS VV MM) (hc : Cst a)
    (hflag : a.env t0=(frameFlag bits).toNat)
    (hin : C.inp.drop a.ip=framePayload bits++rest)
    (hcursor : a.rc store=(a.ram store).length)
    (hfit : a.env payloadLengthVar+bits.length<2^C.Wd) :
    Hs C (.loop (.eq t0 v1) (countedFrameBody store)) a (10*bits.length+2) (fun b=>
      b.env t0=0 ∧ b.env payloadLengthVar=a.env payloadLengthVar+bits.length ∧
      b.ip=a.ip+2*bits.length ∧ b.ram store=a.ram store++bits.map Bool.toNat ∧
      b.rc store=a.rc store+bits.length ∧
      (∀ other,other≠store→b.ram other=a.ram other ∧ b.rc other=a.rc other) ∧
      (b.out,b.kin,b.kout,b.kc)=(a.out,a.kin,a.kout,a.kc) ∧
      Cst b ∧ Fr a b [t0,t1,payloadLengthVar]) := by
  induction bits generalizing a with
  | nil =>
      have he : (Cnd.eq t0 v1).eval a=false := by simp [Cnd.eval,hflag,frameFlag,hc.one]
      refine ⟨a,2,Ex.loopF (show t0≠v1 by decide) he,by simp,?_⟩
      exact ⟨by simpa [frameFlag] using hflag,by simp,by simp,by simp,by simp,
        fun _ _=>⟨rfl,rfl⟩,rfl,hc,Fr.refl _ _⟩
  | cons bit bits ih =>
      have he : (Cnd.eq t0 v1).eval a=true := by simp [Cnd.eval,hflag,frameFlag,hc.one]
      have hinput : C.inp.drop a.ip=bit::frameFlag bits::(framePayload bits++rest) := by
        change C.inp.drop a.ip=(bit::frame bits)++rest at hin
        rw [frame_decompose bits] at hin
        simpa only [List.cons_append] using hin
      obtain ⟨b,n,eb,hn,hb⟩:=frameReadBody_spec C store a bit (frameFlag bits)
        (framePayload bits++rest) hinput hcursor
      subst b
      let d:=(frameReadStep a store bit (frameFlag bits)).set payloadLengthVar
        ((frameReadStep a store bit (frameFlag bits)).env payloadLengthVar+1)
      have hdlen : d.env payloadLengthVar=a.env payloadLengthVar+1 := by
        simp (config:={decide:=true}) [d,frameReadStep,DS.set]
      have eInc:=OpEx.inc (C:=C) payloadLengthVar
        (frameReadStep a store bit (frameFlag bits)) (by
          simpa (config:={decide:=true}) [frameReadStep] using
            (show a.env payloadLengthVar+1<2^C.Wd by simp only [List.length_cons] at hfit;omega))
      have eBody : Ex C (countedFrameBody store) a d (n+1+1) := Ex.seq eb (Ex.op eInc)
      have hdc : Cst d := by
        constructor
        · simpa (config:={decide:=true}) [d,frameReadStep,DS.set] using hc.z
        · simpa (config:={decide:=true}) [d,frameReadStep,DS.set] using hc.one
        · simpa (config:={decide:=true}) [d,frameReadStep,DS.set] using hc.two
      have hdf : Fr a d [t0,t1,payloadLengthVar] := by
        intro target ht
        simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at ht
        simp [d,frameReadStep,DS.set,Function.update_of_ne ht.1,
          Function.update_of_ne ht.2.1,Function.update_of_ne ht.2.2]
      have hdinput : C.inp.drop d.ip=framePayload bits++rest := by
        change C.inp.drop (a.ip+2)=_
        rw [←List.drop_drop,hinput]
        rfl
      have hdcursor : d.rc store=(d.ram store).length := by
        simp only [d,DS.set_rc,DS.set_ram,frameReadStep,Function.update_self,
          List.length_append,List.length_singleton,hcursor]
      obtain ⟨last,k,ek,hk,hlzero,hllen,hlip,hlram,hlrc,hlother,hlrest,hlc,hlf⟩:=
        ih d hdc (by simp (config:={decide:=true}) [d,frameReadStep,DS.set]) hdinput
          hdcursor (by rw [hdlen];simp only [List.length_cons] at hfit;omega)
      refine ⟨last,(n+1+1)+k+2,Ex.loopT (show t0≠v1 by decide) he eBody ek,?_,
        hlzero,?_,?_,?_,?_,?_,hlrest,hlc,hdf.trans hlf⟩
      · simp only [List.length_cons]
        omega
      · rw [hllen,hdlen]
        simp only [List.length_cons]
        omega
      · rw [hlip]
        change a.ip+2+2*bits.length=a.ip+2*(bit::bits).length
        simp only [List.length_cons]
        omega
      · rw [hlram]
        simp [d,frameReadStep,List.map_cons,List.append_assoc]
      · rw [hlrc]
        simp only [d,DS.set_rc,frameReadStep,Function.update_self,List.length_cons]
        omega
      · intro other hother
        simpa only [d,DS.set_ram,DS.set_rc,frameReadStep,Function.update_of_ne hother]
          using hlother other hother

end NearQuarticWires.StageFormulaMetadata
