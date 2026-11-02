import Proof.Quartic.StagePrint.TranslationMemory

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint.Header
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells

/-- `imp:partition` and `lem:print`, paper/paper.tex: the actual retained witness bits determine the translation number by a paid binary-prefix loop. -/
def translationLoop (store : Fin MM) : St VV MM := forS index count (translationBody store)

/-- `prop:time`, paper/paper.tex: repeated memory access is charged by its actual rewind and prefix length, never by the exponential numerical syndrome value. -/
def translationCost (cursor n : ℕ) : ℕ := n*(cursor+6*n+21)+4

/-- `imp:partition` and `lem:print`, paper/paper.tex: the complete binary prefix is computed from the physically retained witness store, preserving every source bit and all parameter data. -/
theorem translationLoop_run (C : Ctx) (store : Fin MM) (bits : List Bool) (n : ℕ)
    (a : DS VV MM) (hc : Cst a) (hmem : a.ram store=bits.map Bool.toNat)
    (hn : n≤bits.length) (hcount : a.env count=n) (hz : a.env translation=0)
    (hp : a.env power=1) (hcap : 2^n<2^C.Wd) :
    Hs C (translationLoop store) a (translationCost (a.rc store) n) (fun b=>
      b.env translation=binaryPrefix bits n ∧ b.env power=2^n ∧
      b.ip=a.ip ∧ b.out=a.out ∧ b.ram=a.ram ∧
      (b.kin,b.kout,b.kc)=(a.kin,a.kout,a.kc) ∧ Cst b ∧
      Fr a b (index::translationScratch)) := by
  let I : ℕ→DS VV MM→Prop:=fun k b=>
    b.env translation=binaryPrefix bits k ∧ b.env power=2^k ∧
    b.ip=a.ip ∧ b.out=a.out ∧ b.ram=a.ram ∧ b.rc store≤a.rc store+n+1 ∧
    (b.kin,b.kout,b.kc)=(a.kin,a.kout,a.kc) ∧ Cst b ∧ Fr a b (index::translationScratch)
  have h0 : I 0 a:=by
    refine ⟨?_,?_,rfl,rfl,rfl,by omega,rfl,hc,Fr.refl _ _⟩
    · simpa [binaryPrefix] using hz
    · simpa using hp
  have ef:=forS_spec' (C:=C) index count (by decide) (translationBody store) a n
    (by have:=Nat.lt_two_pow_self (n:=n);omega) I (a.rc store+6*n+17)
    (by
      intro k b v ⟨bv,bp,bi,bo,br,bc,bs,bconst,bfr⟩
      refine ⟨?_,?_,bi,bo,br,bc,bs,?_,?_⟩
      · simpa [translation,index] using bv
      · simpa [power,index] using bp
      · have hf : Fr b (b.set index v) [index] := Fr.set b _ (by simp)
        exact Cst.of_fr bconst hf (by decide)
      · have hf : Fr b (b.set index v) [index] := Fr.set b _ (by simp)
        exact bfr.trans (hf.weaken (by intro y hy;exact List.mem_cons.mpr (Or.inl (List.mem_singleton.mp hy))))) h0 hcount ?_
  · refine ef.mono le_rfl ?_
    rintro b ⟨⟨bv,bp,bi,bo,br,_bc,bs,bconst,bfr⟩,_hi,_hn⟩
    exact ⟨bv,bp,bi,bo,br,bs,bconst,bfr⟩
  · intro k hk b ⟨bv,bp,bi,bo,br,bc,bs,bconst,bfr⟩ bk bcount
    have er:=translationBody_run C store bits k b bconst (by rw [br];exact hmem)
      (by omega) bk bp bv
      ((Nat.pow_le_pow_right (by decide : 1≤(2 : ℕ)) (show k+1≤n by omega)).trans_lt hcap)
    refine er.mono (by omega) ?_
    rintro d ⟨dv,dp,di,do_,dr,drc,ds,dconst,dfr⟩
    refine ⟨⟨dv,dp,di.trans bi,do_.trans bo,dr.trans br,?_,ds.trans bs,dconst,?_⟩,?_,?_⟩
    · rw [drc,Function.update_self]
      omega
    · exact bfr.trans (dfr.weaken (by intro y hy;exact List.mem_cons.mpr (Or.inr hy)))
    · rw [dfr index (by decide)]
      exact bk
    · rw [dfr count (by decide)]
      exact bcount

end NearQuarticWires.StagePrint.Header
