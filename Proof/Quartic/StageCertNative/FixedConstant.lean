import Proof.Gates.Cells.Kit

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicGates.Close.Cells

def constantIncrements (x : Fin VV) : ℕ→St VV MM
  | 0=>skipS
  | n+1=>.seq (.op (.inc x)) (constantIncrements x n)

/-- `lem:print` and `prop:time`, paper/paper.tex: a fixed arithmetic constant is installed by literal
ordinary instructions. Its finite program and clock depend only on
the fixed theorem parameters, never on a supplied source constant. -/
theorem constantIncrements_run (C : Ctx) (x : Fin VV) (hx : x≠vJ)
    (n : ℕ) (a : DS VV MM) (hc : Cst a) (hsafe : x∉[vZ,v1,v2])
    (hfit : a.env x+n<2^C.Wd) :
    Hs C (constantIncrements x n) a (2*n+1) (fun z=>
      z.env x=a.env x+n ∧ z.sh=a.sh ∧ Cst z ∧ Fr a z [x,vJ]) := by
  induction n generalizing a with
  | zero=>
    refine (skip_spec a).mono (by simp) ?_
    rintro z rfl
    refine ⟨?_,rfl,?_,Fr.set a _ (by simp)⟩
    · rw [DS.set_env_ne _ _ hx]
      omega
    · exact Cst.of_fr hc (Fr.set (T:=[vJ]) a 0 (by simp)) (by decide)
  | succ n ih=>
    unfold constantIncrements
    refine (Hs.seq (t2:=2*n+1) (hs_inc C x a (by omega)) ?_).mono (by omega) (fun _ h=>h)
    rintro b rfl
    have hf : Fr a (a.set x (a.env x+1)) [x,vJ] := Fr.set a _ (by simp)
    have hb : Cst (a.set x (a.env x+1)) := Cst.of_fr hc hf (by
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hsafe ⊢
      rcases hsafe with ⟨h0,h1,h2⟩
      exact ⟨by simpa only [List.mem_cons,List.not_mem_nil,or_false,not_or] using
        (show vZ≠x ∧ vZ≠vJ from ⟨Ne.symm h0,by decide⟩),
        by simpa only [List.mem_cons,List.not_mem_nil,or_false,not_or] using
        (show v1≠x ∧ v1≠vJ from ⟨Ne.symm h1,by decide⟩),
        by simpa only [List.mem_cons,List.not_mem_nil,or_false,not_or] using
        (show v2≠x ∧ v2≠vJ from ⟨Ne.symm h2,by decide⟩)⟩)
    refine (ih _ hb (by simp only [DS.set_env_self];omega)).mono le_rfl ?_
    rintro z ⟨zv,zs,zc,zf⟩
    exact ⟨by simpa only [DS.set_env_self,Nat.add_assoc,Nat.add_comm n 1] using zv,
      zs,zc,hf.trans zf⟩

def setFixedConstant (x : Fin VV) (n : ℕ) : St VV MM :=
  .seq (.op (.zero x)) (constantIncrements x n)

theorem setFixedConstant_run (C : Ctx) (x : Fin VV) (hx : x≠vJ)
    (n : ℕ) (a : DS VV MM) (hc : Cst a) (hsafe : x∉[vZ,v1,v2])
    (hfit : n<2^C.Wd) :
    Hs C (setFixedConstant x n) a (2*n+3) (fun z=>
      z.env x=n ∧ z.sh=a.sh ∧ Cst z ∧ Fr a z [x,vJ]) := by
  unfold setFixedConstant
  refine (Hs.seq (t2:=2*n+1) (hs_zero C x a) ?_).mono (by omega) (fun _ h=>h)
  rintro b rfl
  have hf : Fr a (a.set x 0) [x,vJ] := Fr.set a _ (by simp)
  have hb : Cst (a.set x 0) := Cst.of_fr hc (Fr.set (T:=[x]) a 0 (by simp)) (by
    simpa only [List.mem_cons,List.not_mem_nil,or_false,not_or,not_false_eq_true,and_true,ne_eq,
      eq_comm] using hsafe)
  refine (constantIncrements_run C x hx n _ hb hsafe (by simpa only [DS.set_env_self,zero_add] using hfit)).mono le_rfl ?_
  rintro z ⟨zv,zs,zc,zf⟩
  exact ⟨by simpa only [DS.set_env_self,zero_add] using zv,zs,zc,hf.trans zf⟩

end NearQuarticWires.StageCertNative
