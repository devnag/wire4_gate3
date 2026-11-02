import Proof.Quartic.StageCert.DigitPair
import Proof.Quartic.StageCert.ChainFactorDock

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicGates.Close.Cells

/-- `imp:chain` and `eq:testE`, paper/paper.tex: the original active integer rate is retained before scaling
the predecessor's chain bit. -/
def linearRate : Fin VV := ⟨112,by decide⟩

/-- `imp:chain`, `eq:testE` and `lem:print`, paper/paper.tex: read the actual factor at row minus one;
row zero uses the unit rate on its already zero subtrahend. -/
def readDigitRate (store : Fin MM) : St VV MM :=
  .ite (.eq chainRow vZ) (.op (.copy linearRate v1))
    (.seq (.op (.copy sourceRecordLimit chainRow))
      (.seq (.op (.sub sourceRecordLimit v1)) (readSourceRecord store linearRate)))

/-- `eq:testE`, `lem:print` and `prop:time`, paper/paper.tex: digit rates are physical retained-factor
reads at their exact active indices; no rational or factor oracle is used. -/
theorem readDigitRate_run (C : Ctx) (store : Fin MM) (row J : ℕ)
    (factors : List ℕ) (a : DS VV MM) (hc : Cst a)
    (hr : a.env chainRow=row) (hrow : row<J) (hlen : factors.length=J-1)
    (hram : a.ram store=factors) (hcursor : a.rc store≤factors.length)
    (hfit : J≤2^C.Wd) :
    Hs C (readDigitRate store) a (a.rc store+5*factors.length+20) (fun z=>
      z.env linearRate=(if row=0 then 1 else factors.getD (row-1) 0) ∧
      StageLift.memorySourceRest store z=StageLift.memorySourceRest store a ∧
      z.rc store≤factors.length ∧ Cst z ∧
      Fr a z [linearRate,sourceRecordLimit,sourceRecordIndex,sourceRecordDiscard]) := by
  unfold readDigitRate
  refine Hs.ite (t := a.rc store+5*factors.length+19) (c := .eq chainRow vZ)
    (show chainRow≠vZ by decide) ?_ ?_
  · intro he
    have hz : row=0 := by simpa only [Cnd.eval,hr,hc.z,decide_eq_true_eq] using he
    refine (hs_copy C linearRate v1 a (by decide)).mono (by omega) ?_
    rintro z rfl
    exact ⟨by simp [hz,hc.one],rfl,hcursor,
      Cst.of_fr (T := [linearRate]) hc (Fr.set _ _ (by simp)) (by decide),
      Fr.set _ _ (by simp)⟩
  · intro he
    have hn : row≠0 := by simpa only [Cnd.eval,hr,hc.z,decide_eq_false_iff_not] using he
    apply Hx.hs
    refine Hs.then (hs_copy C sourceRecordLimit chainRow a (by decide))
      (fun b hb n1 hn1=>?_)
    subst hb
    let b := a.set sourceRecordLimit (a.env chainRow)
    refine Hs.then (hs_sub C sourceRecordLimit v1 b (by decide) (by
      change a.env v1≤a.env chainRow
      rw [hr,hc.one]
      omega)) (fun d hd n2 hn2=>?_)
    subst hd
    let d := b.set sourceRecordLimit (b.env sourceRecordLimit-b.env v1)
    have df : Fr a d [sourceRecordLimit] :=
      (Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp))
    have dc : Cst d := Cst.of_fr hc df (by decide)
    have di : d.env sourceRecordLimit=row-1 := by
      change a.env chainRow-a.env v1=row-1
      rw [hr,hc.one]
    refine Hs.last (readSourceRecord_run C store linearRate (by decide) d dc (row-1) di
      (by change row-1<(a.ram store).length; rw [hram,hlen]; omega)
      (by omega)) (fun z ⟨zr,zrc,zs,zc,zfr⟩ n3 hn3=>?_)
    refine ⟨⟨?_,zs,by rw [zrc]; omega,zc,
      (df.weaken (by decide)).trans (zfr.weaken (by decide))⟩,?_⟩
    · rw [if_neg hn,zr]
      change (a.ram store).getD (row-1) 0=factors.getD (row-1) 0
      rw [hram]
    · change n3≤a.rc store+5*(row-1)+8 at hn3
      omega

end NearQuarticWires.StageCert.Tokens
