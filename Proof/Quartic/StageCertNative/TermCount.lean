import Proof.Quartic.StageCertNative.Ordinal
import Proof.Quartic.StageCert.MomentSourceRead

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicGates.Close.Cells
open StageCert.Tokens

/-- `eq:testX`–`eq:testPhi` and `prop:time`, paper/paper.tex: the actual loop count is N²
for the population tag and N⁸ for either complete moment tag. -/
def countByTag (N tag : ℕ) : ℕ := if tag=0 then N^2 else N^8

theorem termCount_eq_tag {B1 B2 : ℕ} (r : StageCertificateControl.IndexedRequest B1 B2) :
    termCount r=countByTag r.prepared.selected.1.N r.metadata.tag := by
  rw [←actualOrdinal_metadata]
  unfold termCount countByTag
  cases actualOrdinal r <;> rfl

/-- `lem:print` and `prop:time`, paper/paper.tex: the term loop counter and two local binary
arithmetic registers have fixed finite positions. -/
def termRemaining : Fin VV := ⟨55,by decide⟩
def squareCopy : Fin VV := ⟨86,by decide⟩
def squareResult : Fin VV := ⟨87,by decide⟩

def squareTermCount : St VV MM :=
  .seq (.op (.copy squareCopy termRemaining))
    (.seq (.op (.mul termRemaining squareCopy squareResult))
      (.op (.copy termRemaining squareResult)))

/-- `prop:time`, paper/paper.tex: squaring
the retained binary count executes three actual operations and
preserves the source, stores, tapes and unrelated metadata. -/
theorem squareTermCount_run (C : Ctx) (v : ℕ) (a : DS VV MM)
    (hc : Cst a) (hv : a.env termRemaining=v) (hfit : v^2<2^C.Wd) :
    Hs C squareTermCount a 5 (fun z=>z.env termRemaining=v^2 ∧ z.sh=a.sh ∧ Cst z ∧
      Fr a z [termRemaining,squareCopy,squareResult]) := by
  unfold squareTermCount
  apply Hx.hs
  refine Hs.then (hs_copy C squareCopy termRemaining a (by decide))
    (fun b hb n1 hn1=>?_)
  subst hb
  let b:=a.set squareCopy (a.env termRemaining)
  have bc : Cst b := Cst.of_fr hc (Fr.set _ _ (T:=[squareCopy]) (by simp)) (by decide)
  have bv : b.env termRemaining=v := hv
  have bx : b.env squareCopy=v := hv
  refine Hs.then (hs_mul C termRemaining squareCopy squareResult b
    (by decide) (by decide) (by decide) (by rw [bv,bx]; simpa only [pow_two] using hfit))
    (fun d hd n2 hn2=>?_)
  subst hd
  refine Hs.last (hs_copy C termRemaining squareResult _ (by decide))
    (fun z hz n3 hn3=>?_)
  subst hz
  have hf : Fr a (((a.set squareCopy (a.env termRemaining)).set squareResult
      (b.env termRemaining*b.env squareCopy)).set termRemaining
        (b.env termRemaining*b.env squareCopy)) [termRemaining,squareCopy,squareResult] :=
    (Fr.set _ _ (by simp)).trans ((Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp)))
  refine ⟨⟨?_,rfl,Cst.of_fr hc hf (by decide),hf⟩,by omega⟩
  change b.env termRemaining*b.env squareCopy=v^2
  rw [bv,bx,pow_two]

/-- `eq:testX`–`eq:testPhi`, paper/paper.tex:
BASE branches only on the actual test tag after computing N²;
the two additional binary squares give the exact eight-vertex census. -/
def computeTermCount : St VV MM :=
  .seq (.op (.copy termRemaining patternBase))
    (.seq squareTermCount (.ite (.eq sourceTestTag vZ) skipS
      (.seq squareTermCount squareTermCount)))

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual population/moment count branch is
computed without a supplied census or a unary loop in N. -/
theorem computeTermCount_run (C : Ctx) (N tag : ℕ) (a : DS VV MM)
    (hc : Cst a) (hN : 1≤N) (hb : a.env patternBase=N)
    (htag : a.env sourceTestTag=tag) (hfit : N^8<2^C.Wd) :
    Hs C computeTermCount a 30 (fun z=>z.env termRemaining=countByTag N tag ∧
      z.sh=a.sh ∧ Cst z ∧ Fr a z [termRemaining,squareCopy,squareResult,vJ]) := by
  have h2 : N^2<2^C.Wd := (Nat.pow_le_pow_right hN (by decide : 2≤8)).trans_lt hfit
  have h4 : (N^2)^2<2^C.Wd := by
    rw [←pow_mul]
    exact (Nat.pow_le_pow_right hN (by decide : 2*2≤8)).trans_lt hfit
  unfold computeTermCount
  apply Hx.hs
  refine Hs.then (hs_copy C termRemaining patternBase a (by decide))
    (fun b hb' n1 hn1=>?_)
  subst hb'
  let b:=a.set termRemaining (a.env patternBase)
  have bf : Fr a b [termRemaining,squareCopy,squareResult,vJ] := Fr.set _ _ (by simp)
  have bc : Cst b := Cst.of_fr hc bf (by decide)
  refine Hs.then (squareTermCount_run C N b bc hb h2)
    (fun d ⟨dv,ds,dc,df⟩ n2 hn2=>?_)
  have ad : Fr a d [termRemaining,squareCopy,squareResult,vJ] := bf.trans (df.weaken (by decide))
  have dt : d.env sourceTestTag=tag := (ad _ (by decide)).trans htag
  refine Hs.last (Hs.ite (t:=17) (by change sourceTestTag≠vZ; decide)
    (fun he=>?_) (fun he=>?_)) (fun z hz n3 hn3=>⟨hz,by omega⟩)
  · have ht : tag=0 := by simpa [Cnd.eval,dt,dc.z] using he
    refine (skip_spec d).mono (by omega) ?_
    rintro z rfl
    have hf := ad.trans (Fr.set d 0 (T:=[termRemaining,squareCopy,squareResult,vJ])
      (show vJ∈[termRemaining,squareCopy,squareResult,vJ] by simp))
    refine ⟨?_,ds,Cst.of_fr hc hf (by decide),hf⟩
    change d.env termRemaining=countByTag N tag
    simpa [countByTag,ht] using dv
  · have ht : tag≠0 := by simpa [Cnd.eval,dt,dc.z] using he
    refine (Hs.seq (t1:=5) (t2:=5) (squareTermCount_run C (N^2) d dc dv h4)
      (fun e ⟨ev,es,ec,ef⟩=>?_)).mono (by omega) (fun _ h=>h)
    have h8 : ((N^2)^2)^2<2^C.Wd := by
      rw [←pow_mul,←pow_mul]
      exact hfit
    refine (squareTermCount_run C ((N^2)^2) e ec ev h8).mono le_rfl ?_
    rintro z ⟨zv,zs,zc,zf⟩
    refine ⟨?_,zs.trans (es.trans ds),zc,ad.trans
      ((ef.weaken (by decide)).trans (zf.weaken (by decide)))⟩
    simpa only [countByTag,if_neg ht,←pow_mul] using zv

end NearQuarticWires.StageCertNative
