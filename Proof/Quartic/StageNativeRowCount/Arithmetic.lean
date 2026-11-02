import Proof.Quartic.StageNativeRowCount.Request

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageNativeRowCount

open NearCubicGates.Close.Cells

def countProgram : St VV MM :=
  .seq (.op (.copy halfReg rReg))
  (.seq (.op (.half halfReg))
  (.seq (.op (.mul halfReg bReg countReg))
  (.seq (.op (.mul rReg bReg blockReg))
  (.seq (.op (.copy halfReg nReg))
  (.seq (.op (.sub halfReg blockReg))
  (.seq (.op (.inc halfReg))
  (.seq (.op (.half halfReg))
  (.seq (.op (.add countReg halfReg))
  (.seq (.op (.shl countReg)) (.op (.inc countReg)))))))))))

/-- `imp:pullback` and `prop:time`, paper/paper.tex: bounded binary arithmetic computes the actual native
field count with literal natural subtraction and no parity assumptions. -/
theorem countProgram_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (n r b : ℕ) (hn : a.env nReg=n) (hr : a.env rReg=r) (hb : a.env bReg=b)
    (hrb : r*b≤n) (hcap : 4*n+4<2^C.Wd) :
    Hs C countProgram a 21 (fun d => d.env countReg=countValue n r b ∧
      d.sh=a.sh ∧ Cst d) := by
  change a.env (20 : Fin VV) = n at hn
  change a.env (21 : Fin VV) = r at hr
  change a.env (22 : Fin VV) = b at hb
  have hp : r/2*b≤n := (Nat.mul_le_mul_right b (Nat.div_le_self r 2)).trans hrb
  have hhalf : (n-r*b+1)/2≤n+1 := (Nat.div_le_self _ _).trans (by omega)
  unfold countProgram
  refine Hx.hs (Hs.then (hs_copy C halfReg rReg a (by decide)) ?_)
  rintro d rfl k0 hk0
  refine Hs.then (hs_half C halfReg _) ?_
  rintro d rfl k1 hk1
  refine Hs.then (hs_mul C halfReg bReg countReg _ (by decide) (by decide) (by decide) (by
    simpa (config:={decide:=true}) [DS.set,halfReg,rReg,bReg,hr,hb] using hp.trans_lt (show n<2^C.Wd by omega))) ?_
  rintro d rfl k2 hk2
  refine Hs.then (hs_mul C rReg bReg blockReg _ (by decide) (by decide) (by decide) (by
    simpa (config:={decide:=true}) [DS.set,halfReg,rReg,bReg,countReg,hr,hb] using hrb.trans_lt (show n<2^C.Wd by omega))) ?_
  rintro d rfl k3 hk3
  refine Hs.then (hs_copy C halfReg nReg _ (by decide)) ?_
  rintro d rfl k4 hk4
  refine Hs.then (hs_sub C halfReg blockReg _ (by decide) (by
    simpa (config:={decide:=true}) [DS.set,nReg,rReg,bReg,halfReg,countReg,blockReg,hn,hr,hb] using hrb)) ?_
  rintro d rfl k5 hk5
  refine Hs.then (hs_inc C halfReg _ (by
    simp (config:={decide:=true}) [DS.set,nReg,rReg,bReg,halfReg,countReg,blockReg,hn,hr,hb]
    omega)) ?_
  rintro d rfl k6 hk6
  refine Hs.then (hs_half C halfReg _) ?_
  rintro d rfl k7 hk7
  refine Hs.then (hs_add C countReg halfReg _ (by decide) (by
    simp (config:={decide:=true}) [DS.set,nReg,rReg,bReg,halfReg,countReg,blockReg,hn,hr,hb]
    omega)) ?_
  rintro d rfl k8 hk8
  refine Hs.then (hs_shl C countReg _ (by
    simp (config:={decide:=true}) [DS.set,nReg,rReg,bReg,halfReg,countReg,blockReg,hn,hr,hb]
    omega)) ?_
  rintro d rfl k9 hk9
  refine Hs.last (hs_inc C countReg _ (by
    simp (config:={decide:=true}) [DS.set,nReg,rReg,bReg,halfReg,countReg,blockReg,hn,hr,hb]
    omega)) ?_
  rintro d rfl k10 hk10
  refine ⟨⟨?_,rfl,?_⟩,by omega⟩
  · simp (config:={decide:=true}) [DS.set,nReg,rReg,bReg,halfReg,countReg,blockReg,hn,hr,hb,countValue]
  · constructor
    · simpa (config:={decide:=true}) [DS.set,vZ,nReg,rReg,bReg,halfReg,countReg,blockReg] using hc.z
    · simpa (config:={decide:=true}) [DS.set,v1,nReg,rReg,bReg,halfReg,countReg,blockReg] using hc.one
    · simpa (config:={decide:=true}) [DS.set,v2,nReg,rReg,bReg,halfReg,countReg,blockReg] using hc.two

end NearQuarticWires.StageNativeRowCount
