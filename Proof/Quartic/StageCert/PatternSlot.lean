import Proof.Quartic.StageCert.PatternQuotient

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicGates.Close.Cells

/-- `sec:walks` and `lem:print`, paper/paper.tex: the actual low-first original walk ordinal. -/
def sourceTermIndex : Fin VV := ⟨54,by decide⟩

/-- `sec:walks` and `lem:print`, paper/paper.tex: compute one original walk coordinate from the retained
numeric ordinal, without any decoded pattern list in the input. -/
def readPatternSlot (slot : ℕ) (dst : Fin VV) : St VV MM :=
  .seq (.op (.copy patternRemaining sourceTermIndex))
    (.seq (dividePattern slot)
      (.seq (.op (.dm patternRemaining patternBase patternQuotient patternRemainder))
        (.op (.copy dst patternRemainder))))

/-- `sec:walks`, `lem:print` and `prop:time`, paper/paper.tex: actual quotient/remainder
instructions recover exactly index / N^slot modulo N and preserve
the full original input and retained source stores. -/
theorem readPatternSlot_run (C : Ctx) (N index slot : ℕ) (dst : Fin VV)
    (hdst : dst≠patternRemainder)
    (hconst : vZ∉[dst,patternRemaining,patternQuotient,patternRemainder] ∧
      v1∉[dst,patternRemaining,patternQuotient,patternRemainder] ∧
      v2∉[dst,patternRemaining,patternQuotient,patternRemainder])
    (a : DS VV MM) (hc : Cst a)
    (hN : 0<N) (hb : a.env patternBase=N)
    (hi : a.env sourceTermIndex=index) (hfit : 2*N≤2^C.Wd) :
    Hs C (readPatternSlot slot dst) a (4*slot+7) (fun z=>
      z.env dst=index/N^slot%N ∧ z.sh=a.sh ∧ Cst z ∧
      Fr a z [dst,patternRemaining,patternQuotient,patternRemainder]) := by
  unfold readPatternSlot
  apply Hx.hs
  refine Hs.then (hs_copy C patternRemaining sourceTermIndex a (by decide))
    (fun b hb' n1 hn1=>?_)
  subst hb'
  let b := a.set patternRemaining (a.env sourceTermIndex)
  have bc : Cst b := Cst.of_fr hc (Fr.set _ _ (T := [patternRemaining]) (by simp)) (by decide)
  refine Hs.then (dividePattern_run C N index slot b bc hN
    (by change a.env patternBase=N; exact hb)
    (by change a.env sourceTermIndex=index; exact hi) hfit)
    (fun d ⟨dv,ds,dc,df⟩ n2 hn2=>?_)
  have db : d.env patternBase=N := by rw [df _ (by decide)]; exact hb
  refine Hs.then (hs_dm C patternRemaining patternBase patternQuotient patternRemainder d
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [db]; exact hN) (by rw [db]; exact hfit))
    (fun q hq n3 hn3=>?_)
  subst hq
  refine Hs.last (hs_copy C dst patternRemainder _ hdst)
    (fun z hz n4 hn4=>?_)
  subst hz
  have hf : Fr d
      (((d.set patternQuotient (d.env patternRemaining/d.env patternBase)).set
        patternRemainder (d.env patternRemaining%d.env patternBase)).set dst
        (d.env patternRemaining%d.env patternBase))
      [dst,patternRemaining,patternQuotient,patternRemainder] :=
    (Fr.set _ _ (by simp)).trans ((Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp)))
  refine ⟨⟨?_,ds,Cst.of_fr dc hf hconst,
    (Fr.set _ _ (by simp)).trans ((df.weaken (by simp)).trans hf)⟩,by omega⟩
  simp only [DS.set_env_self]
  rw [dv,db]

end NearQuarticWires.StageCert.Tokens
