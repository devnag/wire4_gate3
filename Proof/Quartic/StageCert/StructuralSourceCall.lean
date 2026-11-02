import Proof.Quartic.StageCert.MomentRequest
import Proof.Quartic.StageMainMask.StructuralFinal
import Proof.Quartic.StageMain.EntryEmit

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open StageMain.Compact StageMain.Controller

/-- `def:mask` and `lem:print`, paper/paper.tex: an actual shared cold structural machine is the only
callee used by the original-walk structural source. -/
noncomputable def structuralSourceCallee (B1 B2 : ℕ) : Callee :=
  ⟨StageMainMask.StructuralRequest B1 B2,StageMainMask.structuralWord,
    StageMainMask.structuralOutput,StageMainMask.structuralBudget,
    StageMainMask.structuralWordFunction B1 B2⟩

/-- `sec:cells` and `def:mask`, paper/paper.tex: the two actual pattern indices of the next original edge. -/
def sourceEdgeLeft : Fin VV := ⟨112,by decide⟩
def sourceEdgeRight : Fin VV := ⟨113,by decide⟩

/-- `def:mask` and `lem:print`, paper/paper.tex: copy the actual retained prep word and physically
encode the two computed pattern indices for the shared cold source. -/
def emitStructuralSource : St VV MM :=
  .seq emitCompact (.seq (emitEntryNatural sourceEdgeLeft) (emitEntryNatural sourceEdgeRight))

/-- `def:mask`, `lem:print` and `prop:time`, paper/paper.tex: the callee input is the
literal original prep word followed by two actual binary pattern indices.
All source copies, record rewinds and callee-input writes are paid. -/
theorem emitStructuralSource_run {B1 B2 : ℕ} (C : Ctx) (r : StageMainMask.StructuralRequest B1 B2)
    (a : DS VV MM) (hc : Cst a) (hkin : a.kin=[])
    (hbits : a.ram compactStore=(Program.prepWord B1 B2 r.call r.witness).map Bool.toNat)
    (hlen : a.env compactLength=(Program.prepWord B1 B2 r.call r.witness).length)
    (hcursor : a.rc compactStore=(Program.prepWord B1 B2 r.call r.witness).length)
    (hleft : a.env sourceEdgeLeft=r.left.val) (hright : a.env sourceEdgeRight=r.right.val)
    (hW : 2≤C.Wd) (hfit : (Program.prepWord B1 B2 r.call r.witness).length<2^C.Wd)
    (hlfit : natBitLength r.left.val+2<2^C.Wd) (hrfit : natBitLength r.right.val+2<2^C.Wd)
    (hroom : (StageMainMask.structuralWord r).length≤C.Lk) :
    Hs C emitStructuralSource a
      (9*(Program.prepWord B1 B2 r.call r.witness).length+
        40*natBitLength r.left.val+40*natBitLength r.right.val+92) (fun z=>
      z.kin=StageMainMask.structuralWord r ∧ z.ip=a.ip ∧ z.out=a.out ∧
      z.ram=a.ram ∧ z.rc=a.rc ∧ z.kout=a.kout ∧ z.kc=a.kc ∧ Cst z ∧
      Fr a z ([c0,t0,t3]++emitNatT)) := by
  let bits := Program.prepWord B1 B2 r.call r.witness
  have hlenRoom : bits.length+(natWord r.left.val).length+(natWord r.right.val).length≤C.Lk := by
    simpa only [StageMainMask.structuralWord,List.length_append,bits] using hroom
  unfold emitStructuralSource
  apply Hx.hs
  refine Hs.then (emitCompact_run C bits a hc hbits hlen hfit
    (by rw [hkin,List.length_nil]; omega))
    (fun b ⟨bk,bi,bo,br,brc,bout,bcursor,bc,bfr⟩ n1 hn1=>?_)
  have bkin : b.kin=bits := by simpa only [hkin,List.nil_append] using bk
  refine Hs.then (emitEntryNatural_run C sourceEdgeLeft (by decide) b bc r.left.val
    ((bfr _ (by decide)).trans hleft) hW hlfit (by rw [bkin]; omega))
    (fun d ⟨dk,ds,dc,dfr⟩ n2 hn2=>?_)
  have dkin : d.kin=bits++natWord r.left.val := by rw [dk,bkin]
  refine Hs.last (emitEntryNatural_run C sourceEdgeRight (by decide) d dc r.right.val
    ((dfr _ (by decide)).trans ((bfr _ (by decide)).trans hright)) hW hrfit
    (by rw [dkin,List.length_append]; exact hlenRoom))
    (fun z ⟨zk,zs,zc,zfr⟩ n3 hn3=>?_)
  have rcbase : Function.update a.rc compactStore bits.length=a.rc := by
    rw [←hcursor]
    exact Function.update_eq_self _ _
  simp only [Prod.mk.injEq] at ds zs
  refine ⟨⟨?_,zs.1.trans (ds.1.trans bi),zs.2.1.trans (ds.2.1.trans bo),
    zs.2.2.1.trans (ds.2.2.1.trans br),zs.2.2.2.1.trans (ds.2.2.2.1.trans (brc.trans rcbase)),
    zs.2.2.2.2.1.trans (ds.2.2.2.2.1.trans bout),
    zs.2.2.2.2.2.trans (ds.2.2.2.2.2.trans bcursor),zc,
    (bfr.weaken (by decide)).trans ((dfr.weaken (by decide)).trans (zfr.weaken (by decide)))⟩,?_⟩
  · rw [zk,dkin]
    rfl
  · rw [hcursor] at hn1
    change n1≤bits.length+8*bits.length+6 at hn1
    dsimp only [bits] at *
    omega

end NearQuarticWires.StageCert.Tokens
