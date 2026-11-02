import Proof.Quartic.StageCert.WeightedOccurrence
import Proof.Quartic.StageCert.CircuitCoefficient

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats

/-- `eq:testE` and `lem:print`, paper/paper.tex: the requested digit row is retained outside coefficient scratch. -/
def requestedChainRow : Fin VV := ⟨82,by decide⟩

/-- `eq:testE`, paper/paper.tex: the positive summand is
the literal current retained chain bit, with the original absent-row zero. -/
def sourceDigitPositive (bits : List Bool) (G row J k g : ℕ) : ℕ :=
  if row<J then (bits.getD ((row+1)*G+k+g) false).toNat else 0

/-- `eq:testE`, paper/paper.tex: the negative summand is
the literal predecessor bit multiplied by the original retained factor. -/
def sourceDigitNegative (bits : List Bool) (factors : List ℕ) (G row J k g : ℕ) : ℕ :=
  predecessorBit bits G row J k g*(if row=0 then 1 else factors.getD (row-1) 0)

/-- `sec:cells` and `lem:print`, paper/paper.tex: signed summands use the exact zero extension of the
selected circuit in the original concatenated occurrence pool. -/
def selectedSummand (circuit firstCount g value : ℕ) : ℕ :=
  if (if circuit=0 then g<firstCount else firstCount≤g) then value else 0

/-- `lem:print`, paper/paper.tex: all per-occurrence
coefficient and edge scratch is disjoint from the original loop index,
requested row, fixed source metadata and source-controller counters. -/
def digitOccurrenceScratch : List (Fin VV) :=
  [savedChainRow,chainRow,linearPositive,linearNegative,linearRate,linearProduct,
    sourceRecordLimit,atomValue,sourceRecordIndex,sourceRecordDiscard,cachedPositive,cachedNegative]++
    weightedEdgeScratch++[vJ]

/-- `eq:testE` and `lem:print`, paper/paper.tex: restore the requested row, read its complete actual digit
coefficient, filter its original bank and emit all eight signed edges. -/
def emitDigitOccurrence (witnessStore ratesStore : Fin MM) : St VV MM :=
  .seq (.op (.copy chainRow requestedChainRow))
    (.seq (loadDigitCoefficient witnessStore ratesStore)
      (.seq zeroOutsideCircuit emitOccurrenceEdges))

/-- `eq:testE`, `lem:print` and `prop:time`, paper/paper.tex: one complete original digit occurrence
is physically emitted from the retained witness, retained factor list,
actual circuit boundary and sign ordinal, without a supplied coefficient. -/
theorem emitDigitOccurrence_run (C : Ctx) (witnessStore ratesStore : Fin MM)
    (hne : witnessStore≠ratesStore) (G row J k g circuit firstCount code Bcoef Batom : ℕ)
    (bits : List Bool) (factors : List ℕ) (a : DS VV MM) (hc : Cst a)
    (hG : 1≤G) (hgG : g<G) (hb : a.env atomCount=G)
    (hr : a.env requestedChainRow=row) (hJ : a.env chainRows=J)
    (hk : a.env selectionStart=k) (hg : a.env atomOccurrence=g)
    (hcirc : a.env selectedCircuit=circuit) (hfirst : a.env firstGateCount=firstCount)
    (hcode : a.env newtonTau=code) (hrow : row<J) (hlen : factors.length=J-1)
    (hram : a.ram witnessStore=bits.map Bool.toNat) (hfr : a.ram ratesStore=factors)
    (hcursor : a.rc witnessStore≤bits.length) (hfcur : a.rc ratesStore≤factors.length)
    (hbits : k+(J+1)*G≤bits.length) (hbound : k+(J+1)*G≤2^C.Wd)
    (hfit : J≤2^C.Wd)
    (hratefit : (if row=0 then 1 else factors.getD (row-1) 0)<2^C.Wd)
    (hW : 5≤C.Wd) (hindex : 17*G<2^C.Wd)
    (hB : ∀edge j,natBitLength (cornerRoleCode edge j*G+g)≤Batom)
    (hAtomFit : Batom+2<2^C.Wd)
    (hCoef : natBitLength (((selectedSummand circuit firstCount g
      (sourceDigitPositive bits G row J k g):ℤ)-selectedSummand circuit firstCount g
      (sourceDigitNegative bits factors G row J k g)).natAbs)≤Bcoef)
    (hCoefFit : Bcoef+2<2^C.Wd) :
    Hs C (emitDigitOccurrence witnessStore ratesStore) a
      (a.rc witnessStore+a.rc ratesStore+11*bits.length+5*factors.length+
        8*(40*Bcoef+160*Batom+640)+140) (fun z=>
      z.out=a.out++(toks (occurrenceWalkFormula G g hgG
          ((selectedSummand circuit firstCount g (sourceDigitPositive bits G row J k g):ℤ)-
            selectedSummand circuit firstCount g (sourceDigitNegative bits factors G row J k g)) code)).flatMap tokWord ∧
      (z.ip,z.ram,z.kin,z.kout,z.kc)=(a.ip,a.ram,a.kin,a.kout,a.kc) ∧
      z.rc witnessStore≤bits.length ∧ z.rc ratesStore≤factors.length ∧ Cst z ∧
      Fr a z digitOccurrenceScratch) := by
  let P := sourceDigitPositive bits G row J k g
  let N := sourceDigitNegative bits factors G row J k g
  let Ps := selectedSummand circuit firstCount g P
  let Ns := selectedSummand circuit firstCount g N
  unfold emitDigitOccurrence
  apply Hx.hs
  refine Hs.then (hs_copy C chainRow requestedChainRow a (by decide))
    (fun b hb' n1 hn1=>?_)
  subst hb'
  let b := a.set chainRow (a.env requestedChainRow)
  have bfr : Fr a b [chainRow] := Fr.set _ _ (by simp)
  have bc : Cst b := Cst.of_fr hc bfr (by decide)
  refine Hs.then (loadDigitCoefficient_run C witnessStore ratesStore hne
    G row J k g bits factors b bc hG hgG ((bfr _ (by decide)).trans hb)
    (by change a.env requestedChainRow=row; exact hr) ((bfr _ (by decide)).trans hJ)
    ((bfr _ (by decide)).trans hk) ((bfr _ (by decide)).trans hg)
    hrow hlen hram hfr hcursor hfcur hbits hbound hfit hratefit)
    (fun d ⟨dp,dn,ds,dwrc,dfrc,dc,dfr⟩ n2 hn2=>?_)
  have df : Fr a d digitOccurrenceScratch :=
    (bfr.weaken (by decide)).trans (dfr.weaken (by decide))
  refine Hs.then (zeroOutsideCircuit_run C circuit firstCount g P N d dc
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
  refine ⟨⟨by simpa only [eo] using zo,?_,by rw [zrc]; exact dwrc,
    by rw [zrc]; exact dfrc,zc,ef.trans (zfr.weaken (by decide))⟩,?_⟩
  · simp only [coefficientSourceRest,DS.sh,Prod.mk.injEq] at ds es
    simp only [Prod.mk.injEq] at zs ⊢
    exact ⟨zs.1.trans (es.1.trans ds.1),zs.2.1.trans (es.2.2.1.trans ds.2.2.1),
      zs.2.2.2.1.trans (es.2.2.2.2.1.trans ds.2.2.2.1),
      zs.2.2.2.2.1.trans (es.2.2.2.2.2.1.trans ds.2.2.2.2.1),
      zs.2.2.2.2.2.trans (es.2.2.2.2.2.2.trans ds.2.2.2.2.2)⟩
  · change n2≤a.rc witnessStore+a.rc ratesStore+11*bits.length+5*factors.length+100 at hn2
    omega

end NearQuarticWires.StageCert.Tokens
