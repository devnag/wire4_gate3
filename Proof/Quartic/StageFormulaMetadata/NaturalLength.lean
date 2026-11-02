import Proof.Quartic.StageFormulaMetadata.TrackedNatural
import Proof.Gates.Cells.Arith
import Proof.Gates.Cells.InputLen

set_option autoImplicit false

namespace NearQuarticWires.StageFormulaMetadata

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells

/-- `lem:print`, paper/paper.tex: the natural
codec has one bit at zero and the usual binary size elsewhere. -/
theorem naturalBits_eq_size {value : ℕ} (hvalue : value≠0) :
    natBitLength value=Nat.size value := by
  apply Nat.le_antisymm
  · exact nbl_le_of_lt (Nat.lt_size_self value) (by
      have :=Nat.size_pos.mpr (Nat.pos_of_ne_zero hvalue)
      omega)
  · exact Nat.size_le.mpr (lt_natBitLength value)

/-- `lem:print`, paper/paper.tex: determine the
canonical natural-field length from its actual binary value. -/
def naturalLength (source : Fin VV) : St VV MM :=
  .seq (sizeP source fieldBytesVar)
    (.seq (.ite (.eq fieldBytesVar vZ) (.op (.inc fieldBytesVar)) skipS)
      (.seq (.op (.shl fieldBytesVar)) (.op (.inc fieldBytesVar))))

/-- `prop:time`, paper/paper.tex: the codec
length scan uses binary halving, including a bounded zero case. -/
theorem naturalLength_spec (C : Ctx) (source : Fin VV)
    (hs : source∉[aw0,fieldBytesVar]) (a : DS VV MM) (hc : Cst a)
    (hfit : (natWord (a.env source)).length<2^C.Wd) :
    Hs C (naturalLength source) a (5*natBitLength (a.env source)+20) (fun b=>
      b.env fieldBytesVar=(natWord (a.env source)).length ∧
      b.sh=a.sh ∧ Cst b ∧ Fr a b [aw0,fieldBytesVar,vJ]) := by
  have hsa : source≠aw0 := by intro h;subst source;exact hs (by decide)
  have hsf : source≠fieldBytesVar := by intro h;subst source;exact hs (by decide)
  have hsize : Nat.size (a.env source)≤natBitLength (a.env source) :=
    Nat.size_le.mpr (lt_natBitLength _)
  have hbits : 2*natBitLength (a.env source)+1<2^C.Wd := by
    simpa only [natWord_length] using hfit
  unfold naturalLength
  refine (Hs.seq (t2:=6) (sizeP_spec source fieldBytesVar hsa (by decide) (by decide)
    a hc (by omega)) fun b ⟨hb,hbsh,hbf⟩=>?_).mono (by omega) (fun _ h=>h)
  have hbc:=Cst.of_fr hc hbf (by decide)
  have eBits : Hs C (.ite (.eq fieldBytesVar vZ) (.op (.inc fieldBytesVar)) skipS) b 2
      (fun d=>d.env fieldBytesVar=natBitLength (a.env source) ∧ d.sh=b.sh ∧
        Cst d ∧ Fr b d [fieldBytesVar,vJ]) := by
    by_cases hzero : a.env source=0
    · have hz : b.env fieldBytesVar=0 := by simpa [hzero] using hb
      refine (Hs.iteT (c:=.eq fieldBytesVar vZ) (show fieldBytesVar≠vZ by decide)
        (by simp [Cnd.eval,hz,hbc.z]) (hs_inc C fieldBytesVar b (by rw [hz];omega))).mono
          le_rfl ?_
      rintro d rfl
      exact ⟨by simp [hzero,hz,natBitLength],rfl,
        Cst.of_fr hbc (Fr.set b _ (T:=[fieldBytesVar]) (by decide)) (by decide),
        Fr.set b _ (by decide)⟩
    · have heq:=naturalBits_eq_size hzero
      have hpos : 0<b.env fieldBytesVar := by
        rw [hb]
        exact Nat.size_pos.mpr (Nat.pos_of_ne_zero hzero)
      refine (Hs.iteF (c:=.eq fieldBytesVar vZ) (show fieldBytesVar≠vZ by decide)
        (by simp [Cnd.eval,hbc.z,Nat.ne_of_gt hpos]) (skip_spec b)).mono le_rfl ?_
      rintro d rfl
      exact ⟨by simpa only [DS.set_env_ne _ _ (show fieldBytesVar≠vJ by decide),heq] using hb,
        rfl,Cst.of_fr hbc (Fr.set b _ (T:=[vJ]) (by decide)) (by decide),Fr.set b _ (by decide)⟩
  refine Hs.seq (t2:=3) eBits fun d ⟨hd,hdsh,hdc,hdf⟩=>?_
  refine Hs.seq (t2:=1) (hs_shl C fieldBytesVar d (by rw [hd];omega)) fun e he=>?_
  subst e
  refine (hs_inc C fieldBytesVar _ (by simp only [DS.set_env_self,hd];exact hbits)).mono le_rfl ?_
  rintro e rfl
  refine ⟨by simp only [DS.set_env_self,hd,natWord_length],hdsh.trans hbsh,?_,?_⟩
  · exact Cst.of_fr hdc
      ((Fr.set d _ (T:=[fieldBytesVar]) (by decide)).trans (Fr.set _ _ (by decide))) (by decide)
  · exact (hbf.weaken (by decide)).trans ((hdf.weaken (by decide)).trans
      ((Fr.set d _ (by decide)).trans (Fr.set _ _ (by decide))))

end NearQuarticWires.StageFormulaMetadata
