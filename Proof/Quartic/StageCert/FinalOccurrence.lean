import Proof.Quartic.StageCert.DigitOccurrence

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats

/-- `eq:testPhi`, paper/paper.tex: the literal
scaled final retained chain bit, before its complete signed A offset. -/
def sourceFinalPositive (bits : List Bool) (G J k g M : ℕ) : ℕ :=
  sourceDigitPositive bits G (J-1) J k g*M

/-- `eq:testPhi` and `lem:print`, paper/paper.tex: restore the final row, read the actual scaled bit,
filter its original bank and emit the complete signed edge sum. -/
def emitFinalOccurrence (store : Fin MM) : St VV MM :=
  .seq (.op (.copy chainRow requestedChainRow))
    (.seq (loadFinalCoefficient store) (.seq zeroOutsideCircuit emitOccurrenceEdges))

/-- `eq:testPhi`, `lem:print` and `prop:time`, paper/paper.tex: every final-error occurrence
is physically emitted with its complete original integer coefficient,
actual selected bank and all source records retained before certification. -/
theorem emitFinalOccurrence_run (C : Ctx) (store : Fin MM)
    (G J k g M A circuit firstCount code Bcoef Batom : ℕ)
    (bits : List Bool) (a : DS VV MM) (hc : Cst a)
    (hG : 1≤G) (hgG : g<G) (hb : a.env atomCount=G)
    (hr : a.env requestedChainRow=J-1) (hJ : a.env chainRows=J)
    (hk : a.env selectionStart=k) (hg : a.env atomOccurrence=g)
    (hM : a.env finalScale=M) (hA : a.env finalOffset=A)
    (hcirc : a.env selectedCircuit=circuit) (hfirst : a.env firstGateCount=firstCount)
    (hcode : a.env newtonTau=code)
    (hram : a.ram store=bits.map Bool.toNat) (hcursor : a.rc store≤bits.length)
    (hbits : k+(J+1)*G≤bits.length) (hbound : k+(J+1)*G≤2^C.Wd)
    (hfit : M<2^C.Wd) (hW : 5≤C.Wd) (hindex : 17*G<2^C.Wd)
    (hB : ∀edge j,natBitLength (cornerRoleCode edge j*G+g)≤Batom)
    (hAtomFit : Batom+2<2^C.Wd)
    (hCoef : natBitLength (((selectedSummand circuit firstCount g
      (sourceFinalPositive bits G J k g M):ℤ)-selectedSummand circuit firstCount g A).natAbs)≤Bcoef)
    (hCoefFit : Bcoef+2<2^C.Wd) :
    Hs C (emitFinalOccurrence store) a
      (a.rc store+5*bits.length+8*(40*Bcoef+160*Batom+640)+80) (fun z=>
      z.out=a.out++(toks (occurrenceWalkFormula G g hgG
        ((selectedSummand circuit firstCount g (sourceFinalPositive bits G J k g M):ℤ)-
          selectedSummand circuit firstCount g A) code)).flatMap tokWord ∧
      (z.ip,z.ram,z.kin,z.kout,z.kc)=(a.ip,a.ram,a.kin,a.kout,a.kc) ∧
      z.rc store≤bits.length ∧ Cst z ∧ Fr a z digitOccurrenceScratch) := by
  let P := sourceFinalPositive bits G J k g M
  let Ps := selectedSummand circuit firstCount g P
  let Ns := selectedSummand circuit firstCount g A
  unfold emitFinalOccurrence
  apply Hx.hs
  refine Hs.then (hs_copy C chainRow requestedChainRow a (by decide))
    (fun b hb' n1 hn1=>?_)
  subst hb'
  let b := a.set chainRow (a.env requestedChainRow)
  have bfr : Fr a b [chainRow] := Fr.set _ _ (by simp)
  have bc : Cst b := Cst.of_fr hc bfr (by decide)
  refine Hs.then (loadFinalCoefficient_run C store G J k g M A bits b bc hG hgG
    ((bfr _ (by decide)).trans hb) (by change a.env requestedChainRow=J-1; exact hr)
    ((bfr _ (by decide)).trans hJ) ((bfr _ (by decide)).trans hk)
    ((bfr _ (by decide)).trans hg) ((bfr _ (by decide)).trans hM)
    ((bfr _ (by decide)).trans hA) hram hcursor hbits hbound hfit)
    (fun d ⟨dp,dn,ds,dr,dc,dfr⟩ n2 hn2=>?_)
  have df : Fr a d digitOccurrenceScratch :=
    (bfr.weaken (by decide)).trans (dfr.weaken (by decide))
  refine Hs.then (zeroOutsideCircuit_run C circuit firstCount g P A d dc
    ((df _ (by decide)).trans hcirc) ((df _ (by decide)).trans hfirst)
    ((df _ (by decide)).trans hg) dp dn)
    (fun e ⟨ep,en,es,ec,efr⟩ n3 hn3=>?_)
  have ef : Fr a e digitOccurrenceScratch := df.trans (efr.weaken (by decide))
  refine Hs.last (emitOccurrenceEdges_run C G g Ps Ns code Bcoef Batom e ec
    ((ef _ (by decide)).trans hb) ((ef _ (by decide)).trans hg) hgG ep en
    ((ef _ (by decide)).trans hcode) hW hindex hB hAtomFit hCoef hCoefFit)
    (fun z ⟨zo,zs,zc,zfr⟩ n4 hn4=>?_)
  have eo : e.out=a.out :=
    (congrArg (fun q=>q.2.1) es).trans (congrArg (fun q=>q.2.1) ds)
  have zrc : z.rc=d.rc := (congrArg (fun q=>q.2.2.1) zs).trans
    (congrArg (fun q=>q.2.2.2.1) es)
  refine ⟨⟨by simpa only [eo] using zo,?_,by rw [zrc]; exact dr,
    zc,ef.trans (zfr.weaken (by decide))⟩,?_⟩
  · simp only [StageLift.memorySourceRest,DS.sh,Prod.mk.injEq] at ds es
    simp only [Prod.mk.injEq] at zs ⊢
    exact ⟨zs.1.trans (es.1.trans ds.1),zs.2.1.trans (es.2.2.1.trans ds.2.2.1),
      zs.2.2.2.1.trans (es.2.2.2.2.1.trans ds.2.2.2.2.1),
      zs.2.2.2.2.1.trans (es.2.2.2.2.2.1.trans ds.2.2.2.2.2.1),
      zs.2.2.2.2.2.trans (es.2.2.2.2.2.2.trans ds.2.2.2.2.2.2)⟩
  · change n2≤a.rc store+5*bits.length+40 at hn2
    omega

end NearQuarticWires.StageCert.Tokens
