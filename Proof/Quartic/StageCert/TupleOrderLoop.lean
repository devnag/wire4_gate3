import Proof.Quartic.StageCert.PrefixOrder
import Proof.Quartic.StageCert.TupleArithmetic

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicGates.Close.Cells

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: one actual bounded occurrence tuple is checked by its
radix digits and adjacent comparisons, retaining the full source address. -/
def scanTupleOrder : St VV MM :=
  forS tuplePosition newtonIndex (.seq decodeTupleDigit testTupleDigit)

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: the tuple-order scan changes only its private finite
counter, predecessor, exact radix division scratch and zero-one coefficient. -/
def tupleOrderScratch : List (Fin VV) :=
  [tuplePosition,tuplePrevious,tupleDigit,tupleOrdered,tuplePower,tupleQuotient,tupleRemainder,vJ]

/-- `lem:maskpoly`, `lem:print` and `prop:time`, paper/paper.tex: the full original tuple-order
coefficient is computed by a concrete linear-length binary scan. -/
theorem scanTupleOrder_run (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (G degree address : ℕ) (hG : 1≤G)
    (hb : a.env atomCount=G) (hp : a.env tuplePower=G^degree)
    (ha : a.env tupleAddress=address) (hd : a.env newtonIndex=degree)
    (ho : a.env tupleOrdered=1) (hfit : 2*G^degree≤2^C.Wd) (hdfit : degree<2^C.Wd) :
    Hs C scanTupleOrder a (19*degree+4) (fun z=>
      z.env tupleOrdered=(prefixIncreasingBit
        (fun i=>address/G^(degree-1-i)%G) degree).toNat ∧
      z.sh=a.sh ∧ Cst z ∧ Fr a z tupleOrderScratch) := by
  classical
  let value : ℕ→ℕ := fun i=>address/G^(degree-1-i)%G
  let I : ℕ→DS VV MM→Prop := fun i b=>
    b.env tuplePower=G^(degree-i) ∧
      b.env tupleOrdered=(prefixIncreasingBit value i).toNat ∧
      (i=0 ∨ b.env tuplePrevious=value (i-1)) ∧
      b.sh=a.sh ∧ Cst b ∧ Fr a b tupleOrderScratch
  have hset : ∀ i b v,I i b→I i (b.set tuplePosition v) := by
    rintro i b v ⟨bp,bo,bl,bs,bc,bf⟩
    exact ⟨by simpa only [DS.set_env_ne _ _ (by decide : tuplePower≠tuplePosition)] using bp,
      by simpa only [DS.set_env_ne _ _ (by decide : tupleOrdered≠tuplePosition)] using bo,
      by simpa only [DS.set_env_ne _ _ (by decide : tuplePrevious≠tuplePosition)] using bl,
      bs,Cst.of_fr (T := [tuplePosition]) bc (Fr.set _ _ (by simp)) (by decide),
      bf.trans (Fr.set _ _ (by simp [tupleOrderScratch]))⟩
  have h0 : I 0 a := by
    exact ⟨by simpa using hp,by simpa [prefixIncreasingBit,StrictMono] using ho,
      Or.inl rfl,rfl,hc,Fr.refl _ _⟩
  unfold scanTupleOrder
  refine (forS_spec' (C := C) tuplePosition newtonIndex (by decide)
    (.seq decodeTupleDigit testTupleDigit) a degree hdfit I 15 hset h0 hd ?_).mono (by omega) ?_
  · intro i hi b ⟨bp,bo,bl,bs,bc,bfr⟩ bi bn
    have bG : b.env atomCount=G := (bfr _ (by decide)).trans hb
    have ba : b.env tupleAddress=address := (bfr _ (by decide)).trans ha
    apply Hx.hs
    refine Hs.then (decodeTupleDigit_run C b bc G degree i address hG hi bG bp ba hfit)
      (fun d ⟨dp,dd,ds,dc,dfr⟩ n1 hn1=>?_)
    have doi : d.env tuplePosition=i := (dfr _ (by decide)).trans bi
    have dof : d.env tupleOrdered=(prefixIncreasingBit value i).toNat :=
      (dfr _ (by decide)).trans bo
    have dprevious : i=0 ∨ d.env tuplePrevious=value (i-1) :=
      bl.imp_right (fun h=>(dfr _ (by decide)).trans h)
    refine Hs.last (testTupleDigit_run C d dc (prefixIncreasingBit value i)
      i (d.env tuplePrevious) (value i) dof doi rfl dd)
      (fun z ⟨zo,zprev,zs,zc,zfr⟩ n2 hn2=>?_)
    have zflag : z.env tupleOrdered=(prefixIncreasingBit value (i+1)).toNat := by
      rw [zo]
      apply congrArg Bool.toNat
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true,decide_eq_true_eq,prefixIncreasingBit_true,prefixIncreasing_succ]
      rcases dprevious with hz | hp'
      · simp [hz]
      · simp [hp']
    have zpow : z.env tuplePower=G^(degree-(i+1)) := by
      rw [zfr _ (by decide),dp]
      congr 1
      omega
    refine ⟨⟨⟨zpow,zflag,Or.inr (by simpa only [Nat.add_sub_cancel] using zprev),
      zs.trans (ds.trans bs),zc,
      bfr.trans ((dfr.weaken (by decide)).trans (zfr.weaken (by decide)))⟩,?_,?_⟩,?_⟩
    · rw [zfr _ (by decide),doi]
    · rw [zfr _ (by decide),dfr _ (by decide)]
      exact bn
    · omega
  · rintro z ⟨⟨_,zf,_,zs,zc,zfr⟩,_,_⟩
    exact ⟨zf,zs,zc,zfr⟩

end NearQuarticWires.StageCert.Tokens
