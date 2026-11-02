import Proof.Quartic.StageCert.TupleOrder

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicGates.Close.Cells

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: the current radix positional power is held in binary. -/
def tuplePower : Fin VV := ⟨88,by decide⟩
/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: a tuple address is retained across both its order test and
its original selected-square emission. -/
def tupleAddress : Fin VV := ⟨89,by decide⟩
/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: intermediate radix quotients are exact natural numbers. -/
def tupleQuotient : Fin VV := ⟨90,by decide⟩
/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: discarded Euclidean remainders have private storage. -/
def tupleRemainder : Fin VV := ⟨91,by decide⟩

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: one actual tuple coordinate is extracted from its original
address with three exact Euclidean divisions and a positional update. -/
def decodeTupleDigit : St VV MM :=
  .seq (.op (.dm tuplePower atomCount tupleQuotient tupleRemainder))
    (.seq (.op (.copy tuplePower tupleQuotient))
      (.seq (.op (.dm tupleAddress tuplePower tupleQuotient tupleRemainder))
        (.op (.dm tupleQuotient atomCount tupleRemainder tupleDigit))))

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: dynamic tuple coordinates have their exact original radix
meaning, with a constant operation count and no enumeration oracle. -/
theorem decodeTupleDigit_run (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (G degree position address : ℕ) (hG : 1≤G) (hi : position<degree)
    (hb : a.env atomCount=G) (hp : a.env tuplePower=G^(degree-position))
    (ha : a.env tupleAddress=address) (hfit : 2*G^degree≤2^C.Wd) :
    Hs C decodeTupleDigit a 7 (fun z=>
      z.env tuplePower=G^(degree-1-position) ∧
      z.env tupleDigit=address/G^(degree-1-position)%G ∧
      z.sh=a.sh ∧ Cst z ∧ Fr a z [tuplePower,tupleQuotient,tupleRemainder,tupleDigit]) := by
  have hpow : G^(degree-position)=G^(degree-1-position)*G := by
    rw [←pow_succ]
    congr 1
    omega
  have hpos : 0<G^(degree-1-position) := Nat.pow_pos (by omega)
  have hbase : G≤G^degree := by
    calc
      G=G^1 := (pow_one _).symm
      _≤G^degree := Nat.pow_le_pow_right hG (by omega)
  have hsmall : G^(degree-1-position)≤G^degree := Nat.pow_le_pow_right hG (by omega)
  unfold decodeTupleDigit
  refine Hs.seq (t1 := 1) (t2 := 5)
    (hs_dm C tuplePower atomCount tupleQuotient tupleRemainder a
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by rw [hb]; omega) (by rw [hb]; omega)) ?_
  rintro b rfl
  refine Hs.seq (t1 := 1) (t2 := 3)
    (hs_copy C tuplePower tupleQuotient _ (by decide)) ?_
  rintro d rfl
  have hval : a.env tuplePower/a.env atomCount=G^(degree-1-position) := by
    rw [hp,hb,hpow,Nat.mul_div_cancel _ (by omega)]
  have hval' : a.env tuplePower/G=G^(degree-1-position) := by simpa only [hb] using hval
  refine Hs.seq (t1 := 1) (t2 := 1)
    (hs_dm C tupleAddress tuplePower tupleQuotient tupleRemainder _
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by vsimp [hval]; exact hpos) (by vsimp [hval]; omega)) ?_
  rintro e rfl
  refine (hs_dm C tupleQuotient atomCount tupleRemainder tupleDigit _
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by vsimp [hb]; omega) (by vsimp [hb]; omega)).mono le_rfl ?_
  rintro z rfl
  refine ⟨?_,?_,rfl,?_,?_⟩
  · vsimp [hval]
  · vsimp [hval',ha,hb]
  · exact ⟨by vsimp [tuplePower,tupleQuotient,tupleRemainder,tupleDigit,hc.z],
      by vsimp [tuplePower,tupleQuotient,tupleRemainder,tupleDigit,hc.one],
      by vsimp [tuplePower,tupleQuotient,tupleRemainder,tupleDigit,hc.two]⟩
  · exact (Fr.set _ _ (by simp)).trans ((Fr.set _ _ (by simp)).trans
      ((Fr.set _ _ (by simp)).trans ((Fr.set _ _ (by simp)).trans
        ((Fr.set _ _ (by simp)).trans ((Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp)))))))

end NearQuarticWires.StageCert.Tokens
