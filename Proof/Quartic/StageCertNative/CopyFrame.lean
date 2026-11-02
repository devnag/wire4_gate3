import Proof.Quartic.StageCertNative.CopyBit

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open StageLift

/-- `lem:print`, paper/paper.tex: the raw
payload and following frame marker are both copied, with no decoded
length or altered delimiter. -/
def copyFramePair : St VV MM := .seq copyInputBit copyInputBit

theorem copyFrameLoop_run (C : Ctx) (bits rest : List Bool) (a : DS VV MM) (hc : Cst a)
    (hflag : a.env t0=(frameFlag bits).toNat)
    (hin : C.inp.drop a.ip=framePayload bits++rest) :
    Hs C (.loop (.eq t0 v1) copyFramePair) a (11*bits.length+2) (fun z=>
      z.env t0=0 ∧ z.ip=a.ip+2*bits.length ∧ z.out=a.out++framePayload bits ∧
      (z.ram,z.rc,z.kin,z.kout,z.kc)=(a.ram,a.rc,a.kin,a.kout,a.kc) ∧
      Cst z ∧ Fr a z [t0]) := by
  induction bits generalizing a with
  | nil=>
    have he : (Cnd.eq t0 v1).eval a=false := by
      simp only [Cnd.eval,hflag,frameFlag,List.isEmpty_nil,Bool.not_true,Bool.toNat_false,hc.one]
      decide
    refine ⟨a,2,Ex.loopF (show t0≠v1 by decide) he,by simp,?_,?_,?_,rfl,hc,Fr.refl _ _⟩
    · simpa only [frameFlag,List.isEmpty_nil,Bool.not_true,Bool.toNat_false] using hflag
    · simp only [List.length_nil,mul_zero,add_zero]
    · simp only [framePayload,List.append_nil]
  | cons bit bits ih=>
    have he : (Cnd.eq t0 v1).eval a=true := by
      simp only [Cnd.eval,hflag,frameFlag,List.isEmpty_cons,Bool.not_false,Bool.toNat_true,hc.one]
      decide
    have hinput : C.inp.drop a.ip=bit::frameFlag bits::(framePayload bits++rest) := by
      change C.inp.drop a.ip=(bit::frame bits)++rest at hin
      rw [frame_decompose] at hin
      exact hin
    obtain ⟨b,n1,e1,h1,bv,bi,bo,bs,bc,bf⟩:=copyInputBit_run C a hc bit
      (frameFlag bits::(framePayload bits++rest)) hinput
    have bin : C.inp.drop b.ip=frameFlag bits::(framePayload bits++rest) := by
      rw [bi,←List.drop_drop,hinput]
      rfl
    obtain ⟨d,n2,e2,h2,dv,di,doo,ds,dc,df⟩:=copyInputBit_run C b bc (frameFlag bits)
      (framePayload bits++rest) bin
    have din : C.inp.drop d.ip=framePayload bits++rest := by
      rw [di,←List.drop_drop,bin]
      rfl
    obtain ⟨z,n3,e3,h3,zv,zi,zo,zs,zc,zf⟩:=ih d dc dv din
    refine ⟨z,(n1+n2+1)+n3+2,Ex.loopT (show t0≠v1 by decide) he (Ex.seq e1 e2) e3,?_,zv,?_,?_,
      zs.trans (ds.trans bs),zc,bf.trans (df.trans zf)⟩
    · simp only [List.length_cons]
      omega
    · rw [zi,di,bi]
      simp only [List.length_cons]
      omega
    · rw [zo,doo,bo]
      simp only [List.append_assoc,List.cons_append,List.nil_append,framePayload]
      rw [frame_decompose bits]
      rfl

/-- `lem:print`, paper/paper.tex: one exact
source frame is copied as raw literal bits by its original markers. -/
def copyRawFrame : St VV MM :=
  .seq copyInputBit (.loop (.eq t0 v1) copyFramePair)

theorem copyRawFrame_run (C : Ctx) (bits rest : List Bool) (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip=frame bits++rest) :
    Hs C copyRawFrame a (11*bits.length+7) (fun z=>
      z.ip=a.ip+(frame bits).length ∧ z.out=a.out++frame bits ∧
      (z.ram,z.rc,z.kin,z.kout,z.kc)=(a.ram,a.rc,a.kin,a.kout,a.kc) ∧ Cst z ∧ Fr a z [t0]) := by
  unfold copyRawFrame
  apply Hx.hs
  refine Hs.then (copyInputBit_run C a hc (frameFlag bits) (framePayload bits++rest)
    (by simpa only [frame_decompose,List.cons_append] using hin))
    (fun b ⟨bv,bi,bo,bs,bc,bf⟩ n1 hn1=>?_)
  have bin : C.inp.drop b.ip=framePayload bits++rest := by
    rw [bi,←List.drop_drop,hin,frame_decompose]
    rfl
  refine Hs.last (copyFrameLoop_run C bits rest b bc bv bin)
    (fun z ⟨_zv,zi,zo,zs,zc,zf⟩ n2 hn2=>?_)
  refine ⟨⟨?_,?_,zs.trans bs,zc,bf.trans zf⟩,by omega⟩
  · rw [zi,bi,frame_length]
    omega
  · rw [zo,bo,List.append_assoc]
    rw [frame_decompose bits]
    rfl

end NearQuarticWires.StageCertNative
