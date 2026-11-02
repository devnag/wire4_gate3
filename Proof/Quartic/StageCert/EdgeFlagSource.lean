import Proof.Quartic.StageCert.StructuralFlag

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells
open StageMain.Compact

/-- `def:mask` and `lem:print`, paper/paper.tex: compute one original edge, invoke the concrete cold
incidence/structural source, and emit its actual Boolean reply. -/
def emitEdgeStructural (edge : Fin 8) : St VV MM :=
  .seq (readEdgePatterns edge) (.seq invokeStructuralSource
    (.seq decodeStructuralReply emitStructuralFlag))

/-- `def:mask` and `lem:print`, paper/paper.tex: the complete finite scratch excludes the retained
original ordinal, selected metadata and preparation length. -/
def edgeStructuralScratch : List (Fin VV) :=
  [sourceEdgeLeft,sourceEdgeRight,patternRemaining,patternQuotient,patternRemainder,
    maskStructural,c0,t0,t3]++emitNatT

/-- `def:mask`, `lem:print` and `prop:time`, paper/paper.tex: original prep bytes and
the actual walk ordinal alone determine the emitted structural factor.
The source copy, finite callee work, reply reads and output bit are paid. -/
theorem emitEdgeStructural_run {B1 B2 : ℕ} (r : MomentRequest B1 B2) (edge : Fin 8)
    (width : ℕ) (input : List Bool) (L B : ℕ)
    (a : DS VV MM) (hc : Cst a) (hkin : a.kin=[])
    (hbits : a.ram compactStore=(Program.prepWord B1 B2 r.call r.witness).map Bool.toNat)
    (hlen : a.env compactLength=(Program.prepWord B1 B2 r.call r.witness).length)
    (hcursor : a.rc compactStore=(Program.prepWord B1 B2 r.call r.witness).length)
    (hb : a.env patternBase=r.selected.1.N) (hi : a.env sourceTermIndex=r.index.val)
    (hW : 2≤width) (hfit : (Program.prepWord B1 B2 r.call r.witness).length<2^width)
    (hNfit : 2*r.selected.1.N≤2^width)
    (hlfit : natBitLength (r.edgeRequest edge).left.val+2<2^width)
    (hrfit : natBitLength (r.edgeRequest edge).right.val+2<2^width)
    (hroom : (StageMainMask.structuralWord (r.edgeRequest edge)).length≤L)
    (hbudget : StageMainMask.structuralBudget (r.edgeRequest edge)≤B) :
    Hs (structuralSourceContext B1 B2 width input L B) (emitEdgeStructural edge) a
      (9*(Program.prepWord B1 B2 r.call r.witness).length+
        40*natBitLength (r.edgeRequest edge).left.val+
        40*natBitLength (r.edgeRequest edge).right.val+L+B+180) (fun z=>
      z.out=a.out++[StagePrint.callStructural r.call r.rules r.walk edge] ∧
      z.ip=a.ip ∧ z.ram=a.ram ∧ z.rc=a.rc ∧ z.kin=[] ∧ Cst z ∧
      Fr a z edgeStructuralScratch) := by
  let C := structuralSourceContext B1 B2 width input L B
  unfold emitEdgeStructural
  apply Hx.hs
  refine Hs.then (readEdgePatterns_run C r edge a hc hb hi hNfit)
    (fun b ⟨bl,br,bs,bc,bf⟩ n1 hn1=>?_)
  have bip : b.ip=a.ip := congrArg (fun q=>q.1) bs
  have bout : b.out=a.out := congrArg (fun q=>q.2.1) bs
  have bram : b.ram=a.ram := congrArg (fun q=>q.2.2.1) bs
  have brc : b.rc=a.rc := congrArg (fun q=>q.2.2.2.1) bs
  have bkin : b.kin=a.kin := congrArg (fun q=>q.2.2.2.2.1) bs
  refine Hs.then (invokeStructuralSource_run (r.edgeRequest edge) width input L B b bc
    (bkin.trans hkin) (by rw [bram]; exact hbits) ((bf _ (by decide)).trans hlen)
    (by rw [brc]; exact hcursor) bl br hW hfit hlfit hrfit hroom hbudget)
    (fun d ⟨dk,dkc,dkin,di,dout,dram,drc,dc,df⟩ n2 hn2=>?_)
  have dbytes : d.kout=[true,StageMainMask.structuralBit (r.edgeRequest edge),false] :=
    dk.trans (StageMainMask.structuralOutput_bytes _)
  refine Hs.then (decodeStructuralReply_run C (StageMainMask.structuralBit (r.edgeRequest edge))
    d dc dbytes dkc)
    (fun q ⟨qbit,_,qs,qc,qf⟩ n3 hn3=>?_)
  refine Hs.last (emitStructuralFlag_run C (StageMainMask.structuralBit (r.edgeRequest edge))
    q qc qbit)
    (fun z ⟨zo,zs,ze,zc⟩ n4 hn4=>?_)
  simp only [Prod.mk.injEq] at qs zs
  have efr : Fr q z edgeStructuralScratch := fun x _=>congrFun ze x
  refine ⟨⟨?_,zs.1.trans (qs.1.trans (di.trans bip)),
    zs.2.1.trans (qs.2.2.1.trans (dram.trans bram)),
    zs.2.2.1.trans (qs.2.2.2.1.trans (drc.trans brc)),
    zs.2.2.2.1.trans (qs.2.2.2.2.1.trans dkin),zc,
    (bf.weaken (by decide)).trans ((df.weaken (by decide)).trans
      ((qf.weaken (by decide)).trans efr))⟩,?_⟩
  · rw [zo,qs.2.1]
    rw [dout,bout,r.edgeRequest_bit edge]
  · dsimp only [MomentRequest.edgeRequest] at hn2 ⊢
    omega

end NearQuarticWires.StageCert.Tokens
