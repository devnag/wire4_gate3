import Proof.Quartic.StageLift.FrameRead

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells

/-- `lem:print`, paper/paper.tex: a source
bit is copied by an actual read and actual Boolean output instruction. -/
def copyInputBit : St VV MM := .seq (.op (.rdI t0)) (emitB .emit t0)

theorem copyInputBit_run (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (bit : Bool) (rest : List Bool) (hin : C.inp.drop a.ip=bit::rest) :
    Hs C copyInputBit a 4 (fun z=>
      z.env t0=bit.toNat ∧ z.ip=a.ip+1 ∧ z.out=a.out++[bit] ∧
      (z.ram,z.rc,z.kin,z.kout,z.kc)=(a.ram,a.rc,a.kin,a.kout,a.kc) ∧
      Cst z ∧ Fr a z [t0]) := by
  unfold copyInputBit
  refine Hs.seq (t2:=2) (StageLift.readInputBit_spec C t0 a bit rest hin) ?_
  rintro b rfl
  let b:DS VV MM:={a.set t0 bit.toNat with ip:=a.ip+1}
  have bf : Fr a b [t0] := Fr.set a _ (by simp)
  have bc : Cst b := Cst.of_fr hc bf (by decide)
  refine (emitB_spec (snkO C) t0 (by decide) b bc trivial).mono le_rfl ?_
  rintro z ⟨zo,zs,ze⟩
  have zenv : z.env t0=bit.toNat := (congrFun ze t0).trans rfl
  have zc : Cst z := ⟨by rw [ze];exact bc.z,
    by rw [ze];exact bc.one,by rw [ze];exact bc.two⟩
  have zs0:=congrArg (fun q=>q.1) zs
  have zrest:=congrArg (fun q=>(q.2.1,q.2.2.1,q.2.2.2.1,q.2.2.2.2.1,q.2.2.2.2.2)) zs
  change z.out=b.out++[decide (b.env t0=1)] at zo
  have hzbit : decide (b.env t0=1)=bit := by change decide (bit.toNat=1)=bit;cases bit <;> rfl
  refine ⟨zenv,zs0,?_,zrest,zc,?_⟩
  · rw [zo,hzbit]
    rfl
  · exact bf.trans (fun x _=>congrFun ze x)

end NearQuarticWires.StageCertNative
