import Proof.Quartic.StageCert.DigitCoefficient

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicGates.Close.Cells

/-- `eq:testPhi` and `lem:print`, paper/paper.tex: the literal final scaling factor retained from the
selected parameter record. -/
def finalScale : Fin VV := ⟨114,by decide⟩
/-- `eq:testPhi` and `lem:print`, paper/paper.tex: the original final integer offset is retained exactly. -/
def finalOffset : Fin VV := ⟨113,by decide⟩

/-- `eq:testPhi` and `lem:print`, paper/paper.tex: the last actual chain bit is multiplied by M1 and the
original A is retained as the negative summand, without natural truncation. -/
def loadFinalCoefficient (store : Fin MM) : St VV MM :=
  .seq (readChainRecord store linearPositive)
    (.seq (.op (.mul linearPositive finalScale linearProduct))
      (.seq (.op (.copy linearPositive linearProduct))
        (.op (.copy linearNegative finalOffset))))

/-- `eq:testPhi`, `lem:print` and `prop:time`, paper/paper.tex: the complete original final
coefficient is obtained by a physical retained-source read and exact
binary arithmetic, including every vanishing or negative result. -/
theorem loadFinalCoefficient_run (C : Ctx) (store : Fin MM)
    (G J k g M A : ℕ) (bits : List Bool) (a : DS VV MM) (hc : Cst a)
    (hG : 1≤G) (hgG : g<G) (hb : a.env atomCount=G) (hr : a.env chainRow=J-1)
    (hJ : a.env chainRows=J) (hk : a.env selectionStart=k) (hg : a.env atomOccurrence=g)
    (hM : a.env finalScale=M) (hA : a.env finalOffset=A)
    (hram : a.ram store=bits.map Bool.toNat) (hcursor : a.rc store≤bits.length)
    (hbits : k+(J+1)*G≤bits.length) (hbound : k+(J+1)*G≤2^C.Wd)
    (hfit : M<2^C.Wd) :
    Hs C (loadFinalCoefficient store) a (a.rc store+5*bits.length+40) (fun z=>
      z.env linearPositive=(if J-1<J then (bits.getD ((J-1+1)*G+k+g) false).toNat else 0)*M ∧
      z.env linearNegative=A ∧
      StageLift.memorySourceRest store z=StageLift.memorySourceRest store a ∧
      z.rc store≤bits.length ∧ Cst z ∧
      Fr a z [linearPositive,linearNegative,linearProduct,sourceRecordLimit,atomValue,
        sourceRecordIndex,sourceRecordDiscard]) := by
  let bit := if J-1<J then (bits.getD ((J-1+1)*G+k+g) false).toNat else 0
  have hbit : bit≤1 := by
    dsimp only [bit]
    split_ifs
    · cases bits.getD ((J-1+1)*G+k+g) false <;> decide
    · omega
  unfold loadFinalCoefficient
  apply Hx.hs
  refine Hs.then (readChainRecord_source C store linearPositive (by decide)
    G (J-1) J k g bits a hc hG hgG hb hr hJ hk hg hram hcursor hbits hbound)
    (fun b ⟨bp,bs,br,bc,bfr⟩ n1 hn1=>?_)
  have bm : b.env finalScale=M := (bfr _ (by decide)).trans hM
  refine Hs.then (hs_mul C linearPositive finalScale linearProduct b
    (by decide) (by decide) (by decide) (by
      rw [bp,bm]
      have hh : bit*M≤M := by nlinarith
      exact hh.trans_lt hfit)) (fun d hd n2 hn2=>?_)
  subst hd
  let d := b.set linearProduct (b.env linearPositive*b.env finalScale)
  refine Hs.then (hs_copy C linearPositive linearProduct d (by decide))
    (fun e he n3 hn3=>?_)
  subst he
  let e := d.set linearPositive (d.env linearProduct)
  refine Hs.last (hs_copy C linearNegative finalOffset e (by decide))
    (fun z hz n4 hn4=>?_)
  subst hz
  refine ⟨⟨?_,?_,bs,br,?_,?_⟩,?_⟩
  · change b.env linearPositive*b.env finalScale=bit*M
    rw [bp,bm]
  · change b.env finalOffset=A
    exact (bfr _ (by decide)).trans hA
  · exact Cst.of_fr (T := [linearPositive,linearNegative,linearProduct]) bc
      ((Fr.set _ _ (by simp)).trans ((Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp)))) (by decide)
  · exact (bfr.weaken (by decide)).trans ((Fr.set _ _ (by simp)).trans
      ((Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp))))
  · omega

end NearQuarticWires.StageCert.Tokens
