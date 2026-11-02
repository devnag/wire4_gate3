import Proof.Quartic.StageCert.StructuralSourceCall

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open StageMain.Compact

/-- `def:mask` and `prop:time`, paper/paper.tex: the structural source invokes its already proved
ordinary callee with explicit finite input and work reserves. -/
noncomputable def structuralSourceContext (B1 B2 width : ℕ) (input : List Bool) (L B : ℕ) : Ctx :=
  ⟨width,input,structuralSourceCallee B1 B2,L,B⟩

/-- `def:mask` and `lem:print`, paper/paper.tex: encode one actual original-edge request and execute
the concrete shared structural machine. -/
def invokeStructuralSource : St VV MM := .seq emitStructuralSource (.op .kcall)

/-- `def:mask`, `lem:print` and `prop:time`, paper/paper.tex: actual preparation bytes
and computed pattern indices produce the exact original structural
reply by a paid ordinary-machine call, without an incidence oracle. -/
theorem invokeStructuralSource_run {B1 B2 : ℕ} (r : StageMainMask.StructuralRequest B1 B2)
    (width : ℕ) (input : List Bool) (L B : ℕ)
    (a : DS VV MM) (hc : Cst a) (hkin : a.kin=[])
    (hbits : a.ram compactStore=(Program.prepWord B1 B2 r.call r.witness).map Bool.toNat)
    (hlen : a.env compactLength=(Program.prepWord B1 B2 r.call r.witness).length)
    (hcursor : a.rc compactStore=(Program.prepWord B1 B2 r.call r.witness).length)
    (hleft : a.env sourceEdgeLeft=r.left.val) (hright : a.env sourceEdgeRight=r.right.val)
    (hW : 2≤width) (hfit : (Program.prepWord B1 B2 r.call r.witness).length<2^width)
    (hlfit : natBitLength r.left.val+2<2^width) (hrfit : natBitLength r.right.val+2<2^width)
    (hroom : (StageMainMask.structuralWord r).length≤L)
    (hbudget : StageMainMask.structuralBudget r≤B) :
    Hs (structuralSourceContext B1 B2 width input L B) invokeStructuralSource a
      (9*(Program.prepWord B1 B2 r.call r.witness).length+
        40*natBitLength r.left.val+40*natBitLength r.right.val+L+B+94) (fun z=>
      z.kout=StageMainMask.structuralOutput r ∧ z.kc=0 ∧ z.kin=[] ∧
      z.ip=a.ip ∧ z.out=a.out ∧ z.ram=a.ram ∧ z.rc=a.rc ∧ Cst z ∧
      Fr a z ([c0,t0,t3]++emitNatT)) := by
  let C := structuralSourceContext B1 B2 width input L B
  unfold invokeStructuralSource
  apply Hx.hs
  refine Hs.then (emitStructuralSource_run C r a hc hkin hbits hlen hcursor hleft hright
    hW hfit hlfit hrfit hroom)
    (fun b ⟨bk,bi,bo,br,brc,_,_,bc,bfr⟩ n1 hn1=>?_)
  have hin : b.kin=C.K.inw r := bk
  refine Hs.last (Hs.op (OpEx.kcall (C := C) r b hin hbudget) rfl)
    (fun z hz n2 hn2=>?_)
  subst hz
  exact ⟨⟨rfl,rfl,rfl,bi,bo,br,brc,⟨bc.z,bc.one,bc.two⟩,bfr⟩,by
    change n2≤1+L+B at hn2
    omega⟩

end NearQuarticWires.StageCert.Tokens
