import Proof.Quartic.StageCert.WeightedEdges

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Tabulator

/-- `sec:walks` and `lem:print`, paper/paper.tex: one original occurrence contributes all eight signed
edges on the same unchanged seventeen-role pool. -/
def occurrenceWalkFormula (G g : ℕ) (hg : g<G) (weight : ℤ) (code : ℕ) : Formula (17*G) :=
  Formula.sumList (List.ofFn fun edge : Fin 8=>.mul
    (.const (weight*Cycle.signValue (code.testBit edge.val)))
    (Cells.edgeFormula (by decide : 0<4) edge ⟨g,hg⟩))

/-- `lem:print`, paper/paper.tex: cache one actual
coefficient, initialize the original sign ordinal, and emit its full edge sum. -/
def emitOccurrenceEdges : St VV MM :=
  .seq cacheCoefficientPair (.seq (.op (.copy remainingSigns newtonTau))
    (emitWeightedEdges (List.ofFn fun edge : Fin 8=>edge)))

/-- `lem:print` and `prop:time`, paper/paper.tex: every original occurrence's complete linear contribution
is physically serialized using its loaded signed summands and actual
ordinal, with exact integer tokens and all original source data retained. -/
theorem emitOccurrenceEdges_run (C : Ctx) (G g positive negative code Bcoef Batom : ℕ)
    (a : DS VV MM) (hc : Cst a) (hG : a.env atomCount=G)
    (hg : a.env atomOccurrence=g) (hgG : g<G)
    (hp : a.env linearPositive=positive) (hn : a.env linearNegative=negative)
    (hcode : a.env newtonTau=code) (hW : 5≤C.Wd) (hindex : 17*G<2^C.Wd)
    (hB : ∀edge j,natBitLength (cornerRoleCode edge j*G+g)≤Batom)
    (hAtomFit : Batom+2<2^C.Wd)
    (hCoef : natBitLength (((positive:ℤ)-negative).natAbs)≤Bcoef)
    (hCoefFit : Bcoef+2<2^C.Wd) :
    Hs C emitOccurrenceEdges a (8*(40*Bcoef+160*Batom+640)+30) (fun z=>
      z.out=a.out++(toks (occurrenceWalkFormula G g hgG ((positive:ℤ)-negative) code)).flatMap tokWord ∧
      (z.ip,z.ram,z.rc,z.kin,z.kout,z.kc)=(a.ip,a.ram,a.rc,a.kin,a.kout,a.kc) ∧
      Cst z ∧ Fr a z ([cachedPositive,cachedNegative]++weightedEdgeScratch)) := by
  unfold emitOccurrenceEdges
  apply Hx.hs
  refine Hs.then (cacheCoefficientPair_run C positive negative a hc hp hn)
    (fun b ⟨bp,bn,bs,bc,bfr⟩ n1 hn1=>?_)
  refine Hs.then (hs_copy C remainingSigns newtonTau b (by decide))
    (fun d hd n2 hn2=>?_)
  subst hd
  let d := b.set remainingSigns (b.env newtonTau)
  have df : Fr a d ([cachedPositive,cachedNegative,remainingSigns]) :=
    (bfr.weaken (by simp)).trans (Fr.set _ _ (by simp))
  have dc : Cst d := Cst.of_fr (T := [remainingSigns]) bc (Fr.set _ _ (by simp)) (by decide)
  have ds : d.sh=a.sh := bs
  have dcode : d.env remainingSigns=code/2^0 := by
    change b.env newtonTau=code/2^0
    rw [bfr _ (by decide),hcode]
    simp
  refine Hs.last (emitWeightedEdges_run C (List.ofFn fun edge : Fin 8=>edge)
    0 G g positive negative code Bcoef Batom d dc
    ((df _ (by decide)).trans hG) ((df _ (by decide)).trans hg) hgG
    (by change b.env cachedPositive=positive; exact bp)
    (by change b.env cachedNegative=negative; exact bn) dcode (by decide)
    hW hindex hB hAtomFit hCoef hCoefFit)
    (fun z ⟨zo,_,zs,zc,zfr⟩ n3 hn3=>?_)
  have doo : d.out=a.out := congrArg (fun q=>q.2.1) ds
  have dsource : (d.ip,d.ram,d.rc,d.kin,d.kout,d.kc)=(a.ip,a.ram,a.rc,a.kin,a.kout,a.kc) := by
    simp only [DS.sh,Prod.mk.injEq] at ds ⊢
    exact ⟨ds.1,ds.2.2.1,ds.2.2.2.1,ds.2.2.2.2.1,ds.2.2.2.2.2.1,ds.2.2.2.2.2.2⟩
  refine ⟨⟨?_,zs.trans dsource,zc,
    (df.weaken (by decide)).trans (zfr.weaken (by
      intro y hy
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hy ⊢
      tauto))⟩,?_⟩
  · simpa only [doo,weightedEdgeForms,List.map_ofFn,Function.comp_def,occurrenceWalkFormula] using zo
  · simp only [List.length_ofFn] at hn3
    omega

end NearQuarticWires.StageCert.Tokens
