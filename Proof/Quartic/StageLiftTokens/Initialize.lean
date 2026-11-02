import Proof.Quartic.StageLift.ResidueCacheContract
import Proof.Quartic.StageMain.ParameterGet
import Proof.Quartic.StagePrint.SourceValidity

/-!
# Actual residue-source metadata

`lem:residue`, `lem:print` and Step 3, paper/paper.tex: the selected partition is fetched
from its retained parameter record; chain count and sign ordinal are
copied from their original fixed fields. No coefficient is supplied.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageLiftTokens
open NearCubicGates.Close.Cells StageLift StageCert.Tokens

def initializeResidue : St VV MM :=
  .seq (StageMain.readParameter ⟨6,by decide⟩ selectionStart)
    (.seq (.op (.copy chainRows degreeChain)) (.op (.copy newtonTau signCodeVar)))

theorem initializeResidue_run (C : Ctx) (p : Cells.Parameters) (a : DS VV MM)
    (hc : Cst a) (hram : a.ram parameterStore=parameterScalars p)
    (hJ : a.env degreeChain=p.J) (hW : 3≤C.Wd) :
    Hs C initializeResidue a (a.rc parameterStore+60) (fun z=>
      z.env selectionStart=p.k ∧ z.env chainRows=p.J ∧ z.env newtonTau=a.env signCodeVar ∧
      z.rc parameterStore=7 ∧ StageMain.parameterRest z=StageMain.parameterRest a ∧
      Cst z ∧ Fr a z [t2,vJ,c0,selectionStart,chainRows,newtonTau]) := by
  have hcap : 8≤2^C.Wd := by
    have h := Nat.pow_le_pow_right (by decide : 1≤(2:ℕ)) hW
    norm_num at h
    exact h
  unfold initializeResidue
  apply Hx.hs
  refine Hs.then (StageMain.readParameter_run C p ⟨6,by decide⟩ selectionStart a hc hram
    (by change 6<2^C.Wd; omega) (by decide))
    (fun b ⟨bk,br,bs,bc,bfr⟩ n1 hn1=>?_)
  refine Hs.then (hs_copy C chainRows degreeChain b (by decide))
    (fun d hd n2 hn2=>?_)
  subst hd
  let d := b.set chainRows (b.env degreeChain)
  refine Hs.last (hs_copy C newtonTau signCodeVar d (by decide))
    (fun z hz n3 hn3=>?_)
  subst hz
  have df : Fr b d [chainRows] := Fr.set _ _ (by simp)
  have zf : Fr d (d.set newtonTau (d.env signCodeVar)) [newtonTau] := Fr.set _ _ (by simp)
  have ff : Fr a (d.set newtonTau (d.env signCodeVar))
      [t2,vJ,c0,selectionStart,chainRows,newtonTau] :=
    (bfr.weaken (by decide)).trans ((df.weaken (by decide)).trans (zf.weaken (by decide)))
  refine ⟨⟨?_,?_,?_,br,bs,Cst.of_fr hc ff (by decide),ff⟩,?_⟩
  · rw [zf _ (by decide),df _ (by decide)]
    exact bk
  · rw [zf _ (by decide)]
    change b.env degreeChain=p.J
    exact (bfr _ (by decide)).trans hJ
  · rw [DS.set_env_self,df _ (by decide),bfr _ (by decide)]
  · change n1≤a.rc parameterStore+7*6+13 at hn1
    omega

end NearQuarticWires.StageLiftTokens
