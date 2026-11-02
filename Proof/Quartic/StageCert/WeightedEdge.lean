import Proof.Quartic.StageCert.SignWord

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Tabulator

/-- `sec:walks` and `lem:print`, paper/paper.tex: the next literal signed coefficient multiplies the
complete original four-corner residual on its unchanged atom pool. -/
def emitWeightedEdge (edge : Fin 8) : St VV MM :=
  .seq readNextSign (.seq emitPolarityCoefficient
    (.seq (emitOriginalEdge edge) (StageLift.emitOperator .mul)))

/-- `lem:print`, paper/paper.tex: the exact weighted
edge printer changes only sign-scan, signed-token and atom-index scratch. -/
def weightedEdgeScratch : List (Fin VV) :=
  [remainingSigns,tupleQuotient,selectedTokenBit,linearPositive,linearNegative,
    newtonSignField,newtonMagnitudeField,atomRole,atomValue]++StageLift.tokenScratch

/-- `lem:print` and `prop:time`, paper/paper.tex: one original weighted edge is produced from its actual
ordinal bit and original-pool atom indices, retaining the complete signed
coefficient and every source record before any certification test. -/
theorem emitWeightedEdge_run (C : Ctx) (edge : Fin 8)
    (G g positive negative code Bcoef Batom : ℕ)
    (a : DS VV MM) (hc : Cst a) (hG : a.env atomCount=G)
    (hg : a.env atomOccurrence=g) (hgG : g<G)
    (hp : a.env cachedPositive=positive) (hn : a.env cachedNegative=negative)
    (hs : a.env remainingSigns=code/2^edge.val) (hW : 5≤C.Wd)
    (hindex : 17*G<2^C.Wd)
    (hB : ∀j,natBitLength (cornerRoleCode edge j*G+g)≤Batom)
    (hAtomFit : Batom+2<2^C.Wd)
    (hCoef : natBitLength (((positive:ℤ)-negative).natAbs)≤Bcoef)
    (hCoefFit : Bcoef+2<2^C.Wd) :
    Hs C (emitWeightedEdge edge) a (40*Bcoef+160*Batom+620) (fun z=>
      z.out=a.out++(toks (Formula.mul
        (.const (((positive:ℤ)-negative)*Cycle.signValue (code.testBit edge.val)))
        (Cells.edgeFormula (by decide : 0<4) edge ⟨g,hgG⟩))).flatMap tokWord ∧
      z.env remainingSigns=code/2^(edge.val+1) ∧
      (z.ip,z.ram,z.rc,z.kin,z.kout,z.kc)=(a.ip,a.ram,a.rc,a.kin,a.kout,a.kc) ∧
      Cst z ∧ Fr a z weightedEdgeScratch) := by
  have hfour : 4≤2^C.Wd := by
    have hh := Nat.pow_le_pow_right (show 1≤(2:ℕ) by decide) hW
    norm_num at hh
    omega
  unfold emitWeightedEdge
  apply Hx.hs
  refine Hs.then (readNextSign_run C code edge.val a hc hs hfour)
    (fun b ⟨bnext,bbit,bs,bc,bfr⟩ n1 hn1=>?_)
  have bsource : (b.ip,b.ram,b.rc,b.kin,b.kout,b.kc)=(a.ip,a.ram,a.rc,a.kin,a.kout,a.kc) := by
    simp only [DS.sh,Prod.mk.injEq] at bs ⊢
    exact ⟨bs.1,bs.2.2.1,bs.2.2.2.1,bs.2.2.2.2.1,bs.2.2.2.2.2.1,bs.2.2.2.2.2.2⟩
  have bo : b.out=a.out := congrArg (fun q=>q.2.1) bs
  refine Hs.then (emitPolarityCoefficient_run C positive negative Bcoef (code.testBit edge.val)
    b bc ((bfr _ (by decide)).trans hp) ((bfr _ (by decide)).trans hn)
    bbit (by omega) hCoef hCoefFit)
    (fun d ⟨doo,ds,dc,dfr⟩ n2 hn2=>?_)
  have df : Fr a d weightedEdgeScratch :=
    (bfr.weaken (by decide)).trans (dfr.weaken (by decide))
  refine Hs.then (emitOriginalEdge_run C edge G g Batom d dc
    ((df _ (by decide)).trans hG) ((df _ (by decide)).trans hg)
    hgG hW hindex hB hAtomFit)
    (fun e ⟨eo,es,ec,efr⟩ n3 hn3=>?_)
  refine Hs.last (StageLift.emitOperator_spec C .mul e ec)
    (fun z ⟨zo,zs,zc,zfr⟩ n4 hn4=>?_)
  refine ⟨⟨?_,?_,zs.trans (es.trans (ds.trans bsource)),zc,
    df.trans ((efr.weaken (by decide)).trans (zfr.weaken (by decide)))⟩,?_⟩
  · rw [zo,eo,doo,bo]
    simp only [toks,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
      List.append_assoc]
  · rw [zfr _ (by decide),efr _ (by decide),dfr _ (by decide)]
    exact bnext
  · have hm : 2*(tokWord Tok.mul).length+1=15 := by decide
    rw [hm] at hn4
    omega

end NearQuarticWires.StageCert.Tokens
