import Proof.Quartic.StageCert.MomentSourceBounds

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells
open StageMain.Compact

/-- `def:mask` and `lem:print`, paper/paper.tex: the original source is extended only by the one or
eight actual structural factors computed from that same source. -/
noncomputable def MomentRequest.flaggedWord {B1 B2 : ℕ} (r : MomentRequest B1 B2) : List Bool :=
  r.word++structuralFlagList r (momentFlagEdges r.test)

/-- `lem:print`, paper/paper.tex: the finite
source frontend parses original bytes, copies those identical bytes,
then computes every required structural flag by the actual cold callee. -/
def momentFrontend : St VV MM :=
  .seq readMomentSource (.seq emitMomentSourceCopy emitMomentFlags)

/-- `lem:print` and `prop:time`, paper/paper.tex: all frontend reads, source rewrites, actual structural
calls and output bits have explicit costs; no flag provider is a premise. -/
theorem momentFrontend_run {B1 B2 : ℕ} (r : MomentRequest B1 B2)
    (width : ℕ) (input : List Bool) (L B K : ℕ)
    (hroom : ∀edge,(StageMainMask.structuralWord (r.edgeRequest edge)).length≤L)
    (hbudget : ∀edge,StageMainMask.structuralBudget (r.edgeRequest edge)≤B)
    (hcost : ∀edge,9*(Program.prepWord B1 B2 r.call r.witness).length+
      40*natBitLength (r.edgeRequest edge).left.val+
      40*natBitLength (r.edgeRequest edge).right.val+L+B+180≤K)
    (rest : List Bool) (a : DS VV MM) (hc : Cst a) (hkin : a.kin=[])
    (hin : input.drop a.ip=r.word++rest) (hwidth : r.word.length+2≤width)
    (hempty : ∀store,a.ram store=[] ∧ a.rc store=0) :
    Hs (structuralSourceContext B1 B2 width input L B) momentFrontend a
      (r.readSteps+9*(Program.prepWord B1 B2 r.call r.witness).length+
        6*(40*r.word.length+43)+8*(K+2)+12) (fun z=>
      z.out=a.out++r.flaggedWord ∧ z.ip=a.ip+r.word.length ∧ Cst z) := by
  let C := structuralSourceContext B1 B2 width input L B
  obtain ⟨hW,hfit,hNfit,hlfit,hrfit⟩ := r.source_widths width hwidth
  have hBit : r.word.length+2<2^width :=
    lt_of_le_of_lt hwidth Nat.lt_two_pow_self
  unfold momentFrontend
  apply Hx.hs
  refine Hs.then (readMomentSource_run C r rest a hc hin hwidth hempty)
    (fun b ⟨bd,bi,bs,bc⟩ n1 hn1=>?_)
  refine Hs.then (emitMomentSourceCopy_run C r b bc bd r.word.length
    (fun v hv=>r.value_bits v hv) hW hBit hfit)
    (fun d ⟨dout,ds,dc,df⟩ n2 hn2=>?_)
  have dip : d.ip=b.ip := congrArg (fun q=>q.1) ds
  have dram : d.ram=b.ram := congrArg (fun q=>q.2.1) ds
  have drc : d.rc=b.rc := congrArg (fun q=>q.2.2.1) ds
  have dkin : d.kin=[] := (congrArg (fun q=>q.2.2.2.1) ds).trans
    ((congrArg (fun q=>q.2.1) bs).trans hkin)
  have hindex : b.env sourceTermIndex=r.index.val := bd.fields ⟨5,by decide⟩
  have htag : b.env sourceTestTag=(r.test.metadata r.selected.1).tag := bd.fields ⟨0,by decide⟩
  refine Hs.last (emitMomentFlags_run r width input L B K hW hfit hNfit hlfit hrfit
    hroom hbudget hcost d dc dkin (by rw [dram]; exact bd.compact)
    ((df _ (by decide)).trans bd.compactLength) (by rw [drc]; exact bd.compactCursor)
    ((df _ (by decide)).trans bd.base) ((df _ (by decide)).trans hindex)
    ((df _ (by decide)).trans htag))
    (fun z ⟨zo,zi,_,_,_,zc,_⟩ n3 hn3=>?_)
  refine ⟨⟨?_,zi.trans (dip.trans bi),zc⟩,?_⟩
  · have bout : b.out=a.out := congrArg (fun q=>q.1) bs
    rw [zo,dout,bout]
    exact List.append_assoc _ _ _
  · omega

end NearQuarticWires.StageCert.Tokens
