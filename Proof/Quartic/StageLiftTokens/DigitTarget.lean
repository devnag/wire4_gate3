import Proof.Quartic.StageLiftTokens.ScoreTarget

/-!
# Actual digit-target fetch and prime reduction

`lem:residue` and Step 3, paper/paper.tex: the live row is copied to address scratch, the actual
normalized digit is fetched and divided by the selected prime, and
the resulting residue is emitted with its original integer codec.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageLiftTokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open StageLift StageCert.Tokens

def digitTargetProgram : St VV MM :=
  .seq (.op (.copy targetRow requestedChainRow)) (.seq digitTargetAddress emitDigitTarget)

def digitTargetScratch : List (Fin VV) :=
  [targetRow,targetAddress,targetHeaderSize,vJ,c0,targetRaw,targetQuotient,targetValue]++tokenScratch

theorem digitTarget_run {B1 B2 : ℕ} (C : Ctx) (r : Greedy.PrintRequest B1 B2)
    (a : DS VV MM) (E : ℕ) (h : SourceReady C r a E)
    (j : Fin 2) (row : Fin (r.child.selected.1.J-1+1))
    (hj : a.env targetCircuit=j.val) (hr : a.env requestedChainRow=row.val) :
    Hs C digitTargetProgram a (targetSourceCost E) (fun b=>
      b.out=a.out++tokWord (.const ((r.digits j row % (r.prime^r.child.selected.1.e : ℤ)) % (r.prime:ℤ))) ∧
      SourceReady C r b E ∧ SourceFrame a b ∧ Fr a b digitTargetScratch) := by
  let addr := 10+j.val*r.child.selected.1.J+row.val
  have hrow : row.val<r.child.selected.1.J := by
    have hp:=(Cells.prepare_spec _ r.child.selected.1 r.child.selected.2).J_pos
    have hi:=row.isLt
    omega
  have hi : addr<(normalizedPrintIndex r).length := by
    rw [index_length]
    dsimp [addr]
    have hji:=j.isLt
    nlinarith
  have haddr : addr<2^C.Wd := by
    have hh:=h.target_room
    have hjj:=j.isLt
    dsimp [addr]
    nlinarith
  have hrc : a.rc indexStore≤12+2*r.child.selected.1.J := by
    simpa only [h.indexRecords,index_length] using h.valid.rc_le indexStore
  have hh : Hs C digitTargetProgram a (targetSourceCost E) (fun b=>
      b.out=a.out++tokWord (.const ((r.digits j row % (r.prime^r.child.selected.1.e : ℤ)) % (r.prime:ℤ))) ∧
      b.rc=Function.update a.rc indexStore (addr+1) ∧
      (b.ip,b.ram,b.kin,b.kout,b.kc)=(a.ip,a.ram,a.kin,a.kout,a.kc) ∧
      Cst b ∧ Fr a b digitTargetScratch) := by
    unfold digitTargetProgram
    apply Hx.hs
    refine Hs.then (hs_copy C targetRow requestedChainRow a (by decide))
      (fun d hd n0 hn0=>?_)
    subst hd
    let d := a.set targetRow (a.env requestedChainRow)
    have df : Fr a d [targetRow] := Fr.set _ _ (by simp)
    have dc : Cst d := Cst.of_fr h.constants df (by decide)
    refine Hs.then (digitTargetAddress_spec C d dc r.child.selected.1.J row.val j hrow
      ((df _ (by decide)).trans h.chainCount) hr ((df _ (by decide)).trans hj) h.target_room)
      (fun b ⟨ba,bs,bc,bfr⟩ n1 hn1=>?_)
    have bsrc := Same.of_sh bs
    have bf : Fr a b [targetRow,targetAddress,targetHeaderSize,vJ] :=
      (df.weaken (by decide)).trans (bfr.weaken (by decide))
    have bi : b.env targetAddress<(b.ram indexStore).length := by
      rw [ba,bsrc.ram]
      change addr<(a.ram indexStore).length
      rw [h.indexRecords]
      exact hi
    refine Hs.last (emitDigitTarget_spec C b bc r.prime (Reconstruct.PrintRequest.prime_prime r).pos
      ((bf _ (by decide)).trans h.prime) bi (by rw [ba]; exact haddr)
      (by have hw:=h.width_five; omega) h.prime_room
      (lt_of_le_of_lt (Nat.add_le_add_right h.prime_bits 2) h.bits_room))
      (fun z ⟨zo,zrc,zs,zc,zfr⟩ n2 hn2=>?_)
    refine ⟨⟨?_,?_,?_,zc,(bf.weaken (by decide)).trans (zfr.weaken (by decide))⟩,?_⟩
    · rw [zo,bsrc.out,bsrc.ram,ba]
      change a.out++tokWord (.const (((a.ram indexStore).getD addr 0%r.prime:ℕ):ℤ))=_
      rw [h.indexRecords,normalized_digit_value]
    · rw [zrc,bsrc.rc,ba]
      rfl
    · exact zs.trans (by rw [bsrc.ip,bsrc.ram,bsrc.kin,bsrc.kout,bsrc.kc]; rfl)
    · rw [bsrc.rc,ba] at hn2
      change n2≤a.rc indexStore+5*(10+j.val*r.child.selected.1.J+row.val)+40*natBitLength r.prime+68 at hn2
      have hjj:=j.isLt
      have hjE:=h.chains_bound
      have hb:=h.prime_bits
      have hmul : j.val*r.child.selected.1.J≤r.child.selected.1.J := by
        simpa only [one_mul] using Nat.mul_le_mul_right r.child.selected.1.J (show j.val≤1 by omega)
      unfold targetSourceCost sourceBits at *
      have hp := Nat.le_self_pow (by decide : 2≠0) (E+1)
      nlinarith [Nat.mul_le_mul_left (E+1) hp]
  obtain ⟨b,n,he,hn,bo,brc,bs,bc,bfr⟩:=hh
  have hf : SourceFrame a b := by
    simp only [Prod.mk.injEq] at bs
    refine ⟨bs.2.1,?_,?_,fun x hx=>bfr x ((by decide : ∀x∈sourceRegisters,x∉digitTargetScratch) x hx)⟩
    · intro store hs
      rw [brc,Function.update_of_ne]
      exact fun heq=>hs (by simp [heq])
    · simp only [Prod.mk.injEq]
      exact ⟨bs.1,bs.2.2.1,bs.2.2.2.1,bs.2.2.2.2⟩
  have hv : Valid C b := he.valid (by have hw:=h.width_five; omega)
    (fun s hs=>(wf_out_len C.K.wf s).trans (by omega)) h.valid
  exact ⟨b,n,he,hn,bo,h.of_frame bc hv hf,hf,bfr⟩

end NearQuarticWires.StageLiftTokens
