import Proof.Quartic.StageCert.WeightedEdge

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Tabulator

/-- `sec:walks` and `lem:print`, paper/paper.tex: a literal partial signed edge sum on the original pool. -/
def weightedEdgeForms (G g : ℕ) (hg : g<G) (positive negative code : ℕ)
    (edges : List (Fin 8)) : List (Formula (17*G)) :=
  edges.map fun edge=>.mul
    (.const (((positive:ℤ)-negative)*Cycle.signValue (code.testBit edge.val)))
    (Cells.edgeFormula (by decide : 0<4) edge ⟨g,hg⟩)

/-- `lem:print`, paper/paper.tex: the eight original
signed edge terms are emitted in order and closed by literal additions. -/
def emitWeightedEdges : List (Fin 8)→St VV MM
  | [] => StageLift.emitOperator (.const 0)
  | edge::edges => .seq (emitWeightedEdge edge)
      (.seq (emitWeightedEdges edges) (StageLift.emitOperator .add))

private theorem weightedEdgesCostStep (length M n1 n2 n3 : ℕ)
    (h1 : n1≤M) (h2 : n2≤length*(M+20)+20) (h3 : n3≤11) :
    n1+(n2+n3+1)+1≤(length+1)*(M+20)+20 := by
  rw [Nat.add_mul,Nat.one_mul]
  omega

/-- `lem:print` and `prop:time`, paper/paper.tex: the complete fixed eight-edge sum uses the actual
original sign ordinal, physically emitted coefficients and original
atom indices. No full-center table or supplied edge values are used. -/
theorem emitWeightedEdges_run (C : Ctx) (edges : List (Fin 8))
    (start G g positive negative code Bcoef Batom : ℕ)
    (a : DS VV MM) (hc : Cst a) (hG : a.env atomCount=G)
    (hg : a.env atomOccurrence=g) (hgG : g<G)
    (hp : a.env cachedPositive=positive) (hn : a.env cachedNegative=negative)
    (hs : a.env remainingSigns=code/2^start)
    (horder : edges.map Fin.val=List.range' start edges.length)
    (hW : 5≤C.Wd) (hindex : 17*G<2^C.Wd)
    (hB : ∀edge j,natBitLength (cornerRoleCode edge j*G+g)≤Batom)
    (hAtomFit : Batom+2<2^C.Wd)
    (hCoef : natBitLength (((positive:ℤ)-negative).natAbs)≤Bcoef)
    (hCoefFit : Bcoef+2<2^C.Wd) :
    Hs C (emitWeightedEdges edges) a
      (edges.length*(40*Bcoef+160*Batom+640)+20) (fun z=>
      z.out=a.out++(toks (Formula.sumList
        (weightedEdgeForms G g hgG positive negative code edges))).flatMap tokWord ∧
      z.env remainingSigns=code/2^(start+edges.length) ∧
      (z.ip,z.ram,z.rc,z.kin,z.kout,z.kc)=(a.ip,a.ram,a.rc,a.kin,a.kout,a.kc) ∧
      Cst z ∧ Fr a z weightedEdgeScratch) := by
  induction edges generalizing start a with
  | nil =>
    refine (StageLift.emitOperator_spec C (.const 0) a hc).mono
      (by
        have hh : (tokWord (.const 0)).length=9 := by decide
        rw [hh]
        simp) ?_
    rintro z ⟨zo,zs,zc,zfr⟩
    exact ⟨by simpa [weightedEdgeForms,Formula.sumList,toks] using zo,
      by simpa only [List.length_nil,Nat.add_zero] using (zfr _ (by decide)).trans hs,
      zs,zc,zfr.weaken (by decide)⟩
  | cons edge edges ih =>
    have hpair : edge.val=start ∧ edges.map Fin.val=List.range' (start+1) edges.length := by
      simpa only [List.map_cons,List.length_cons,List.range'_succ,List.cons.injEq] using horder
    have he := hpair.1
    have htail := hpair.2
    unfold emitWeightedEdges
    apply Hx.hs
    refine Hs.then (emitWeightedEdge_run C edge G g positive negative code Bcoef Batom
      a hc hG hg hgG hp hn (by simpa only [he] using hs) hW hindex
      (hB edge) hAtomFit hCoef hCoefFit)
      (fun b ⟨bo,bnext,bs,bc,bfr⟩ n1 hn1=>?_)
    refine Hs.then (ih (start+1) b bc
      ((bfr _ (by decide)).trans hG) ((bfr _ (by decide)).trans hg)
      ((bfr _ (by decide)).trans hp) ((bfr _ (by decide)).trans hn)
      (by simpa only [he] using bnext) htail)
      (fun d ⟨doo,dnext,ds,dc,dfr⟩ n2 hn2=>?_)
    refine Hs.last (StageLift.emitOperator_spec C .add d dc)
      (fun z ⟨zo,zs,zc,zfr⟩ n3 hn3=>?_)
    refine ⟨⟨?_,?_,zs.trans (ds.trans bs),zc,
      bfr.trans (dfr.trans (zfr.weaken (by decide)))⟩,?_⟩
    · rw [zo,doo,bo]
      simp only [weightedEdgeForms,List.map_cons,Formula.sumList,toks,List.flatMap_append,
        List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc]
    · rw [zfr _ (by decide),dnext]
      congr 2
      simp only [List.length_cons]
      omega
    · have ha : 2*(tokWord Tok.add).length+1=11 := by decide
      rw [ha] at hn3
      exact weightedEdgesCostStep edges.length (40*Bcoef+160*Batom+620)
        n1 n2 n3 hn1 (by simpa only [Nat.add_assoc] using hn2) hn3

end NearQuarticWires.StageCert.Tokens
