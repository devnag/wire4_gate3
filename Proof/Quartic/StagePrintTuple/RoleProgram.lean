import Proof.Quartic.StagePrintTuple.RoleData

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells
open StagePrint.Header

attribute [local irreducible] readRoleFields computeRole writeRoleOutput
attribute [local irreducible] RolePacket.values RolePacket.outputValues
  headerEmitCost StageGamma.readFieldsCost natBitLength

/-- `lem:print`, paper/paper.tex:
the complete source-to-role subroutine reads the actual packet,
computes its original occurrence and writes the complete affine header. -/
def roleProgram : St VV MM :=
  .seq readRoleFields (.seq computeRole writeRoleOutput)

/-- `prop:time`, paper/paper.tex: the actual role
subroutine pays the source parser, finite role decoder and every
natural-codec and raw-bit output operation. -/
def RolePacket.steps (r : RolePacket) : ℕ :=
  StageGamma.readFieldsCost r.values + 4506 + headerEmitCost r.outputValues + 14

/-- `lem:print` and `prop:time`, paper/paper.tex: the real encoded source packet produces the
exact original-occurrence prefix and native affine header, retaining
all complete source stores and their cursors. -/
theorem roleProgram_spec (C : Ctx) (r : RolePacket) (rest : List Bool)
    (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip = r.word ++ rest)
    (hfields : ∀ v ∈ r.values, natBitLength v + 2 ≤ C.Wd)
    (hW : 2 ≤ C.Wd) (hpos : 0 < r.radix)
    (hGfit : 2*(r.firstCount+r.secondCount) ≤ 2^C.Wd)
    (hrfit : 2*r.radix ≤ 2^C.Wd) (hsmall : 17 < 2^C.Wd)
    (hout : ∀ v ∈ r.outputValues,natBitLength v+2 < 2^C.Wd) :
    Hs C roleProgram a r.steps (fun b =>
      b.out = a.out ++ r.output ∧
      b.ip = a.ip+r.word.length ∧ b.ram=a.ram ∧ b.rc=a.rc ∧
      (b.kin,b.kout,b.kc)=(a.kin,a.kout,a.kc) ∧ Cst b) := by
  unfold roleProgram
  refine (Hs.seq (t2:=4506+headerEmitCost r.outputValues+13)
    (readRoleFields_spec C r rest a hc hin hfields) ?_).mono
    (by unfold RolePacket.steps;omega) (fun _ h=>h)
  rintro b ⟨hb,hfirst,hsecond,hradix,haddress,hatom,bi,bsh,bc,_bf⟩
  refine Hs.seq (t2:=headerEmitCost r.outputValues+12)
    (computeRole_spec C r b hfirst hsecond hatom hradix haddress
      hpos hGfit hrfit hsmall) ?_
  rintro d ⟨hd,di,dsh,dfr⟩
  have dc : Cst d := Cst.of_fr bc dfr (by decide)
  have db : ∀ j : Fin 7,d.env (baseHeaderRegisters[j.val]'(by
      simp [baseHeaderRegisters]))=r.scalars j := by
    intro j
    rw [dfr _ (by fin_cases j <;> decide)]
    exact hb j
  have dm := roleOutput_map r d db di hd
  have ed := writeRoleOutput_spec C d dc hW (by
    intro x hx
    apply hout
    rw [←dm]
    exact List.mem_map.mpr ⟨x,hx,rfl⟩)
  rw [dm] at ed
  refine ed.mono le_rfl ?_
  rintro out ⟨oo,os,oc,_ofr⟩
  have do_ : d.out=b.out := congrArg (fun t=>t.2.1) dsh
  have dip : d.ip=b.ip := congrArg (fun t=>t.1) dsh
  have dram : d.ram=b.ram := congrArg (fun t=>t.2.2.1) dsh
  have drc : d.rc=b.rc := congrArg (fun t=>t.2.2.2.1) dsh
  have ds : (d.kin,d.kout,d.kc)=(b.kin,b.kout,b.kc) :=
    congrArg (fun t=>(t.2.2.2.2.1,t.2.2.2.2.2.1,t.2.2.2.2.2.2)) dsh
  have bo : b.out=a.out := congrArg (fun t=>t.1) bsh
  refine ⟨?_,(congrArg (fun t=>t.1) os).trans (dip.trans bi),
    (congrArg (fun t=>t.2.1) os).trans (dram.trans (congrArg (fun t=>t.2.1) bsh)),
    (congrArg (fun t=>t.2.2.1) os).trans (drc.trans (congrArg (fun t=>t.2.2.1) bsh)),
    (congrArg (fun t=>(t.2.2.2.1,t.2.2.2.2.1,t.2.2.2.2.2)) os).trans
      (ds.trans (congrArg (fun t=>(t.2.2.2.1,t.2.2.2.2.1,t.2.2.2.2.2)) bsh)),oc⟩
  rw [oo,roleOutput_flags r d hd,do_,bo]
  simp only [RolePacket.output,List.append_assoc]

end NearQuarticWires.StageTuple
