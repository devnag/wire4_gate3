import Proof.Quartic.StageLiftMasks.Capacity
import Proof.Quartic.StageCert.MaskParameters

/-!
# Real mask parameter reload after a structural call

`def:mask` and `lem:print`, paper/paper.tex: the original cutoff, degree limit and selection
offset are read from their retained scalar records while the newly
computed structural factor remains in its register.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageLiftMasks
open NearCubicGates.Close.Cells StageLift StageCert.Tokens

theorem loadMaskParameters_ready {B1 B2 width L B : ℕ} (input : List Bool)
    (r : Greedy.PrintRequest B1 B2) (index : Fin (r.child.cellCall.seed.N^8))
    (a : DS VV MM) (h : PrintMasksReady width input L B r index a) :
    Hs (structuralSourceContext B1 B2 width input L B) loadMaskParameters a 316 (fun b=>
      b.out=a.out ∧ PrintMasksReady width input L B r index b ∧ MaskFrame a b ∧
      b.env newtonTau=r.child.selected.1.tau ∧ b.env maskLimit=r.child.selected.1.Xmax+1 ∧
      b.env selectionStart=r.child.selected.1.k ∧ b.env maskStructural=a.env maskStructural) := by
  let C:=structuralSourceContext B1 B2 width input L B
  have hcap:=source_mask_capacity r width h.residue.width
  have hrc : a.rc parameterStore≤46 := by
    simpa only [h.residue.parameterRecords,parameterScalars_length] using h.residue.valid.rc_le parameterStore
  obtain ⟨b,n,he,hn,bt,bx,bk,_br,bs,bc,bfr⟩:=loadMaskParameters_run C r.child.selected.1
    a h.residue.constants h.residue.parameterRecords hcap.minWidth hcap.limit
  simp only [StageMain.parameterRest,Prod.mk.injEq] at bs
  have hf : MaskFrame a b := by
    refine ⟨bs.2.2.1,?_,bs.1,?_⟩
    · intro s hs
      have hs0 : s≠parameterStore := by intro he; subst s; exact hs (by simp)
      simpa only [Function.update_of_ne hs0] using congrFun bs.2.2.2.1 s
    · intro x hx
      exact bfr x ((show ∀x∈maskRegisters,x∉[t2,vJ,c0,newtonTau,maskLimit,selectionStart] by decide) x hx)
  have hkin : b.kin=[] := bs.2.2.2.2.1.trans h.inputEmpty
  exact ⟨b,n,he,by omega,bs.2.1,ready_of_frame h bc (ready_execution_valid h he) hf hkin,
    hf,bt,bx,bk,bfr _ (by decide)⟩

end NearQuarticWires.StageLiftMasks
