import Proof.Quartic.StageCert.MomentSourceRead
import Proof.Quartic.StageMainMask.StoredWord
import Proof.Quartic.StageLift.RawHeader

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open StageMain.Compact

/-- `lem:print`, paper/paper.tex: copy the original
finite preparation word and re-emit its six actually parsed scalar
fields before appending the computed structural factors. -/
def emitMomentSourceCopy : St VV MM :=
  .seq (StageMainMask.emitStoredWord compactStore compactLength)
    (StageLift.emitNaturalFields momentSourceFields)

/-- `lem:print` and `prop:time`, paper/paper.tex: the physical source copy preserves all retained input,
has the identical canonical bytes, and charges every binary write. -/
theorem emitMomentSourceCopy_run {B1 B2 : ℕ} (C : Ctx) (r : MomentRequest B1 B2)
    (a : DS VV MM) (hc : Cst a) (hd : MomentSourceData r a) (B : ℕ)
    (hvalues : ∀v∈r.sourceValues,natBitLength v≤B)
    (hW : 2≤C.Wd) (hBit : B+2<2^C.Wd)
    (hfit : (Program.prepWord B1 B2 r.call r.witness).length<2^C.Wd) :
    Hs C emitMomentSourceCopy a
      (9*(Program.prepWord B1 B2 r.call r.witness).length+6*(40*B+43)+8) (fun z=>
      z.out=a.out++r.word ∧
      (z.ip,z.ram,z.rc,z.kin,z.kout,z.kc)=(a.ip,a.ram,a.rc,a.kin,a.kout,a.kc) ∧
      Cst z ∧ Fr a z ([c0,t0]++StageLift.tokenScratch)) := by
  unfold emitMomentSourceCopy
  apply Hx.hs
  refine Hs.then (StageMainMask.emitStoredWord_run C compactStore compactLength (by decide)
    (Program.prepWord B1 B2 r.call r.witness) a hc hd.compact hd.compactLength hfit)
    (fun b ⟨bo,bi,bkin,bram,brc,bk,bkc,bc,bf⟩ n1 hn1=>?_)
  have bfields (i : Fin 6) : b.env momentSourceFields[i]=r.sourceValues[i] :=
    (bf _ (by fin_cases i <;> decide)).trans (hd.fields i)
  have hbs : ∀x∈momentSourceFields,natBitLength (b.env x)≤B := by
    intro x hx
    obtain ⟨i,hxi⟩ := List.mem_iff_get.mp hx
    have hv := bfields i
    fin_cases i <;> dsimp only [momentSourceFields,MomentRequest.sourceValues] at hxi hv
    all_goals
      simp only [Fin.getElem_fin] at hv
      norm_num at hxi hv
      subst x
      exact (congrArg natBitLength hv).trans_le (hvalues _ (by simp [MomentRequest.sourceValues]))
  refine Hs.last (StageLift.emitNaturalFields_spec C momentSourceFields b bc B (by
    intro x hx
    simp only [momentSourceFields,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl <;> decide) hbs hW hBit)
    (fun z ⟨zo,zs,zc,zf⟩ n2 hn2=>?_)
  have hr : Function.update a.rc compactStore (Program.prepWord B1 B2 r.call r.witness).length=a.rc := by
    rw [←hd.compactCursor]
    exact Function.update_eq_self _ _
  have bvalues : momentSourceFields.flatMap (fun x=>natWord (b.env x))=
      r.sourceValues.flatMap natWord := by
    have h0 := bfields ⟨0,by decide⟩
    have h1 := bfields ⟨1,by decide⟩
    have h2 := bfields ⟨2,by decide⟩
    have h3 := bfields ⟨3,by decide⟩
    have h4 := bfields ⟨4,by decide⟩
    have h5 := bfields ⟨5,by decide⟩
    simp only [momentSourceFields,MomentRequest.sourceValues,Fin.getElem_fin,List.getElem_cons_zero,
      List.getElem_cons_succ] at h0 h1 h2 h3 h4 h5
    simp only [momentSourceFields,MomentRequest.sourceValues,List.flatMap_cons,List.flatMap_nil,
      List.append_nil,h0,h1,h2,h3,h4,h5]
  simp only [Prod.mk.injEq] at zs
  have hrest : (z.ip,z.ram,z.rc,z.kin,z.kout,z.kc)=(a.ip,a.ram,a.rc,a.kin,a.kout,a.kc) := by
    simp only [Prod.mk.injEq]
    exact ⟨zs.1.trans bi,zs.2.1.trans bram,zs.2.2.1.trans (brc.trans hr),
      zs.2.2.2.1.trans bkin,zs.2.2.2.2.1.trans bk,zs.2.2.2.2.2.trans bkc⟩
  refine ⟨⟨?_,hrest,
    zc,(bf.weaken (by intro x hx; exact List.mem_append_left _ hx)).trans
      (zf.weaken (by intro x hx; exact List.mem_append_right _ hx))⟩,?_⟩
  · rw [zo,bo,bvalues,r.word_source_layout,List.append_assoc]
  · rw [hd.compactCursor] at hn1
    change n2≤6*(40*B+43)+1 at hn2
    omega

end NearQuarticWires.StageCert.Tokens
