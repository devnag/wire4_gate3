import Proof.Quartic.StageLiftMasks.Capacity
import Proof.Quartic.StageLiftMasks.Transport
import Proof.Quartic.StageMain.ParameterGet

/-!
# Reloading the original edge-source metadata

`def:mask` and `lem:print`, paper/paper.tex: each structural query reloads its actual radix from
parameter slot seven and its source length from the retained measured
length. Tuple workspace from the preceding mask is not reused as data.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageLiftMasks
open NearCubicGates.Close.Cells StageLift StageCert.Tokens StageMain.Compact

def prepareEdgeSource : St VV MM :=
  .seq (StageMain.readParameter ⟨7,by decide⟩ patternBase)
    (.op (.copy compactLength preparedLength))

theorem prepareEdgeSource_run {B1 B2 width L B : ℕ} (input : List Bool)
    (r : Greedy.PrintRequest B1 B2) (index : Fin (r.child.cellCall.seed.N^8))
    (a : DS VV MM) (h : PrintMasksReady width input L B r index a) :
    Hs (structuralSourceContext B1 B2 width input L B) prepareEdgeSource a 110 (fun b=>
      b.out=a.out ∧ PrintMasksReady width input L B r index b ∧ MaskFrame a b ∧
      b.env patternBase=r.child.selected.1.N ∧ b.env compactLength=(preparedWordOf r).length) := by
  let C:=structuralSourceContext B1 B2 width input L B
  have hcap:=source_mask_capacity r width h.residue.width
  have h32 : 32≤2^width := by
    have hh:=Nat.pow_le_pow_right (by decide : 1≤(2:ℕ)) hcap.minWidth
    norm_num at hh
    exact hh
  have hrc : a.rc parameterStore≤46 := by
    simpa only [h.residue.parameterRecords,parameterScalars_length] using h.residue.valid.rc_le parameterStore
  have hh : Hs C prepareEdgeSource a 110 (fun d=>
      d.out=a.out ∧ d.kin=[] ∧ MaskFrame a d ∧ Cst d ∧
      d.env patternBase=r.child.selected.1.N ∧ d.env compactLength=(preparedWordOf r).length) := by
    unfold prepareEdgeSource
    apply Hx.hs
    refine Hs.then (StageMain.readParameter_run C r.child.selected.1 ⟨7,by decide⟩
      patternBase a h.residue.constants h.residue.parameterRecords
      (by change 7<2^width; omega) (by decide))
      (fun b ⟨bn,_bcursor,bs,bc,bfr⟩ n1 hn1=>?_)
    refine Hs.last (hs_copy C compactLength preparedLength b (by decide))
      (fun d hd n2 hn2=>?_)
    subst hd
    let d:=b.set compactLength (b.env preparedLength)
    have df : Fr b d [compactLength] := Fr.set _ _ (by simp)
    have ff : Fr a d [t2,vJ,c0,patternBase,compactLength] :=
      (bfr.weaken (by decide)).trans (df.weaken (by decide))
    simp only [StageMain.parameterRest,Prod.mk.injEq] at bs
    have hf : MaskFrame a d := by
      refine ⟨bs.2.2.1,?_,bs.1,?_⟩
      · intro s hs
        have hs0 : s≠parameterStore := by intro he; subst s; exact hs (by simp)
        have hcurs:=congrFun bs.2.2.2.1 s
        change b.rc s=a.rc s
        simpa only [Function.update_of_ne hs0] using hcurs
      · intro x hx
        exact ff x ((show ∀x∈maskRegisters,x∉[t2,vJ,c0,patternBase,compactLength] by decide) x hx)
    refine ⟨⟨bs.2.1,bs.2.2.2.2.1.trans h.inputEmpty,hf,Cst.of_fr h.residue.constants ff (by decide),?_,?_⟩,?_⟩
    · exact (df _ (by decide)).trans bn
    · exact (bfr _ (by decide)).trans h.preparedBytes
    · change n1≤a.rc parameterStore+7*7+13 at hn1
      omega
  obtain ⟨b,n,he,hn,bo,bkin,bf,bc,bN,bP⟩:=hh
  exact ⟨b,n,he,hn,bo,ready_of_frame h bc (ready_execution_valid h he) bf bkin,bf,bN,bP⟩

end NearQuarticWires.StageLiftMasks
