import Proof.Quartic.StageLift.MemoryVariable

set_option autoImplicit false

namespace NearQuarticWires.StageFormulaMetadata

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells
open StageLift

/-- `lem:print`, paper/paper.tex: the source
byte cursor and most recent field length are retained binary values. -/
def consumedVar : Fin VV := 85
def fieldBytesVar : Fin VV := 92

/-- `lem:print`, paper/paper.tex: decode one
actual stored natural and add its complete codec length to the cursor. -/
def readTrackedNatural (store : Fin MM) (target : Fin VV) : St VV MM :=
  .seq (readMemoryNatural store)
    (.seq (.op (.copy target t3))
      (.seq (.op (.copy fieldBytesVar t4))
        (.seq (.op (.shl fieldBytesVar))
          (.seq (.op (.inc fieldBytesVar)) (.op (.add consumedVar fieldBytesVar))))))

/-- `lem:print` and `prop:time`, paper/paper.tex: field size is obtained from the actual binary decoder;
every cursor update is a bounded binary operation. -/
theorem readTrackedNatural_spec (C : Ctx) (store : Fin MM) (bits : List Bool)
    (a : DS VV MM) (hc : Cst a) (ha : a.ram store=bits.map Bool.toNat)
    (target : Fin VV) (ht : target∉vZ::v1::v2::consumedVar::fieldBytesVar::rdNatT)
    (value : ℕ) (rest : List Bool)
    (hin : bits.drop (a.rc store)=natWord value++rest)
    (hwidth : natBitLength value+2≤C.Wd)
    (hfit : a.env consumedVar+(natWord value).length<2^C.Wd) :
    Hs C (readTrackedNatural store target) a (30*natBitLength value+40) (fun b=>
      b.env target=value ∧ b.env fieldBytesVar=(natWord value).length ∧
      b.env consumedVar=a.env consumedVar+(natWord value).length ∧
      b.rc store=a.rc store+(natWord value).length ∧
      memorySourceRest store b=memorySourceRest store a ∧ Cst b ∧
      Fr a b (target::consumedVar::fieldBytesVar::rdNatT)) := by
  have htt3 : target≠t3 := by intro h;subst target;exact ht (by decide)
  have htc : target≠consumedVar := by intro h;subst target;exact ht (by decide)
  have htb : target≠fieldBytesVar := by intro h;subst target;exact ht (by decide)
  have htconst : vZ≠target ∧ v1≠target ∧ v2≠target := by
    refine ⟨?_,?_,?_⟩ <;> intro h <;> subst target <;> exact ht (by decide)
  have hlen : 2*natBitLength value+1<2^C.Wd := by
    rw [natWord_length] at hfit
    omega
  unfold readTrackedNatural
  refine (Hs.seq (t2:=9) (readMemoryNatural_spec C store bits a hc ha value rest hin hwidth)
    fun b ⟨hbv,hbl,hbcursor,hbrest,hbf⟩=>?_).mono (by omega) (fun _ h=>h)
  have hbc := Cst.of_fr hc hbf (by decide)
  have hbcons : b.env consumedVar=a.env consumedVar := hbf _ (by decide)
  refine Hs.seq (t2:=7) (hs_copy C target t3 b htt3) fun d hd=>?_
  subst d
  let d:=b.set target (b.env t3)
  refine Hs.seq (t2:=5) (hs_copy C fieldBytesVar t4 d (by decide)) fun e he=>?_
  subst e
  let e:=d.set fieldBytesVar (d.env t4)
  have htt4 : t4≠target := fun h=>ht (h.symm ▸ by decide)
  have ht4 : d.env t4=b.env t4 := by simp only [d,DS.set_env_ne _ _ htt4]
  have helen : e.env fieldBytesVar=natBitLength value := by
    simpa only [e,DS.set_env_self,ht4] using hbl
  refine Hs.seq (t2:=3) (hs_shl C fieldBytesVar e (by rw [helen]; omega)) fun f hf=>?_
  subst f
  let f:=e.set fieldBytesVar (2*e.env fieldBytesVar)
  have hflen : f.env fieldBytesVar=2*natBitLength value := by simp [f,helen]
  refine Hs.seq (t2:=1) (hs_inc C fieldBytesVar f (by rw [hflen]; exact hlen)) fun g hg=>?_
  subst g
  let g:=f.set fieldBytesVar (f.env fieldBytesVar+1)
  have hglen : g.env fieldBytesVar=(natWord value).length := by
    simp [g,hflen]
  have hgcons : g.env consumedVar=a.env consumedVar := by
    simp only [g,f,e,d,DS.set_env_ne _ _ (show consumedVar≠fieldBytesVar by decide),
      DS.set_env_ne _ _ htc.symm,hbcons]
  refine (hs_add C consumedVar fieldBytesVar g (by decide)
    (by rw [hgcons,hglen];exact hfit)).mono le_rfl ?_
  rintro last rfl
  have hframe : Fr b g [target,fieldBytesVar] :=
    (Fr.set b _ (by simp)).trans
      ((Fr.set d _ (by simp)).trans
        ((Fr.set e _ (by simp)).trans (Fr.set f _ (by simp))))
  have hlast : Fr g (g.set consumedVar (g.env consumedVar+g.env fieldBytesVar))
      [consumedVar] := Fr.set _ _ (by simp)
  refine ⟨?_,?_,by simp [hgcons,hglen],?_,?_,?_,?_⟩
  · simp only [DS.set_env_ne _ _ htc]
    simp only [g,f,e,d,DS.set_env_ne _ _ htb,DS.set_env_self]
    exact hbv
  · simpa only [DS.set_env_ne _ _ (show fieldBytesVar≠consumedVar by decide)] using hglen
  · exact hbcursor
  · exact hbrest
  · exact Cst.of_fr hbc ((hframe.weaken (T':=[target,fieldBytesVar,consumedVar])
      (by simp)).trans (hlast.weaken (by simp)))
      (by simp (config:={decide:=true}) [htconst.1,htconst.2.1,htconst.2.2])
  · exact (hbf.weaken (by
      intro y hy
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hy)))).trans
      ((hframe.weaken (by simp)).trans (hlast.weaken (by simp)))

end NearQuarticWires.StageFormulaMetadata
