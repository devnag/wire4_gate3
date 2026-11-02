import Proof.Quartic.StageLiftTokens.TargetBounds

/-!
# Actual score-target fetch and emission

`lem:residue` and Step 3, paper/paper.tex: compute the score address from the live circuit and
chain counters, fetch its actual normalized record, and emit the
canonical integer token while retaining all original sources.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageLiftTokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open StageLift StageCert.Tokens

def scoreTargetProgram : St VV MM := .seq scoreTargetAddress emitScoreTarget

def scoreTargetScratch : List (Fin VV) := [targetAddress,targetHeaderSize,vJ,c0,targetRaw]++tokenScratch

def targetSourceCost (E : ℕ) : ℕ := 10^4*(E+1)^3

theorem scoreTarget_run {B1 B2 : ℕ} (C : Ctx) (r : Greedy.PrintRequest B1 B2)
    (a : DS VV MM) (E : ℕ) (h : SourceReady C r a E)
    (j : Fin 2) (hj : a.env targetCircuit=j.val) :
    Hs C scoreTargetProgram a (targetSourceCost E) (fun b=>
      b.out=a.out++tokWord (.const (r.residues j % (r.prime^r.child.selected.1.e : ℤ))) ∧
      SourceReady C r b E ∧ SourceFrame a b ∧ Fr a b scoreTargetScratch) := by
  let addr := 10+2*r.child.selected.1.J+j.val
  have hi : addr<(normalizedPrintIndex r).length := by
    rw [index_length]
    dsimp [addr]
    have hji:=j.isLt
    omega
  have haddr : addr<2^C.Wd := by have hh:=h.target_room; have hjj:=j.isLt; dsimp [addr]; omega
  have hrc : a.rc indexStore≤12+2*r.child.selected.1.J := by
    simpa only [h.indexRecords,index_length] using h.valid.rc_le indexStore
  have hh : Hs C scoreTargetProgram a (targetSourceCost E) (fun b=>
      b.out=a.out++tokWord (.const (r.residues j % (r.prime^r.child.selected.1.e : ℤ))) ∧
      b.rc=Function.update a.rc indexStore (addr+1) ∧
      (b.ip,b.ram,b.kin,b.kout,b.kc)=(a.ip,a.ram,a.kin,a.kout,a.kc) ∧
      Cst b ∧ Fr a b scoreTargetScratch) := by
    unfold scoreTargetProgram
    apply Hx.hs
    refine Hs.then (scoreTargetAddress_spec C a h.constants r.child.selected.1.J j
      h.chainCount hj h.target_room) (fun b ⟨ba,bs,bc,bfr⟩ n1 hn1=>?_)
    have bsrc := Same.of_sh bs
    have bi : b.env targetAddress<(b.ram indexStore).length := by
      rw [ba,bsrc.ram,h.indexRecords]
      exact hi
    refine Hs.last (emitScoreTarget_spec C b bc (sourceBits E) bi (by rw [ba]; exact haddr)
      (by have hw:=h.width_five; omega) (by rw [bsrc.ram,h.indexRecords,ba]; exact h.score_bits j)
      h.bits_room) (fun z ⟨zo,zrc,zs,zc,zfr⟩ n2 hn2=>?_)
    refine ⟨⟨?_,?_,?_,zc,(bfr.weaken (by decide)).trans (zfr.weaken (by decide))⟩,?_⟩
    · rw [zo,bsrc.out,bsrc.ram,h.indexRecords,ba,normalized_score_value]
    · rw [zrc,bsrc.rc,ba]
    · exact zs.trans (by rw [bsrc.ip,bsrc.ram,bsrc.kin,bsrc.kout,bsrc.kc])
    · rw [bsrc.rc,ba] at hn2
      have hjj:=j.isLt
      have hjE:=h.chains_bound
      unfold targetSourceCost
      dsimp only [sourceBits] at hn2
      have hp := Nat.le_self_pow (by decide : 2≠0) (E+1)
      nlinarith [Nat.mul_le_mul_left (E+1) hp]
  obtain ⟨b,n,he,hn,bo,brc,bs,bc,bfr⟩:=hh
  have hf : SourceFrame a b := by
    simp only [Prod.mk.injEq] at bs
    refine ⟨bs.2.1,?_,?_,fun x hx=>bfr x ((by decide : ∀x∈sourceRegisters,x∉scoreTargetScratch) x hx)⟩
    · intro store hs
      rw [brc,Function.update_of_ne]
      exact fun heq=>hs (by simp [heq])
    · simp only [Prod.mk.injEq]
      exact ⟨bs.1,bs.2.2.1,bs.2.2.2.1,bs.2.2.2.2⟩
  have hv : Valid C b := he.valid (by have hw:=h.width_five; omega)
    (fun s hs=>(wf_out_len C.K.wf s).trans (by omega)) h.valid
  exact ⟨b,n,he,hn,bo,h.of_frame bc hv hf,hf,bfr⟩

end NearQuarticWires.StageLiftTokens
