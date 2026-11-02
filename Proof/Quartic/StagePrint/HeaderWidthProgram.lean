import Proof.Quartic.StagePrint.WidthArithmetic

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint.Header
open NearCubicWires
open NearCubicGates.Close.Cells

/-- `lem:print` and `imp:pullback`, paper/paper.tex: binary size is physically computed before both signed widths. -/
def headerWidthProgram : St VV MM := .seq (sizeP arity sizeVar) widthArithmetic

/-- `lem:print` and `imp:pullback`, paper/paper.tex: the retained original dimension alone determines both complete physical width fields; no width or logarithm is supplied. -/
theorem headerWidthProgram_run (C : Ctx) (a : DS VV MM) (hc : Cst a) (n : ℕ)
    (hn : a.env arity=n) (hcap : 4*(n+1)^2+n+20<2^C.Wd) :
    Hs C headerWidthProgram a (5*Nat.size n+109) (fun b=>
      b.env Lin=(4*n+1)*Nat.clog 2 (n+1)+5 ∧
      b.env Lout=(4*n+1)*Nat.clog 2 (n+1)+5+n+6 ∧
      b.sh=a.sh ∧ Cst b ∧ Fr a b [aw0,sizeVar,work,Lin,Lout]) := by
  have hsle : Nat.size n≤n := Nat.size_le.mpr (Nat.lt_two_pow_self (n:=n))
  have es:=sizeP_spec (C:=C) arity sizeVar (by decide) (by decide) (by decide) a hc
    (by rw [hn];omega)
  rw [hn] at es
  unfold headerWidthProgram
  refine (Hs.seq (t2:=100) es ?_).mono (by omega) (fun _ h=>h)
  rintro b ⟨bs,bsh,bfr⟩
  have bc : Cst b:=Cst.of_fr hc bfr (by decide)
  have bn : b.env arity=n := by rw [bfr arity (by decide)];exact hn
  have eb:=widthArithmetic_run C b bc n (Nat.size n) bn bs (by omega) hcap
  refine eb.mono le_rfl ?_
  rintro d ⟨dl,dr,dsh,dc,dfr⟩
  refine ⟨?_,?_,dsh.trans bsh,dc,?_⟩
  · simpa only [clog_two_succ_eq_size] using dl
  · simpa only [clog_two_succ_eq_size] using dr
  · exact (bfr.weaken (by intro y hy;simp only [List.mem_cons,List.not_mem_nil,or_false] at *;tauto)).trans
      (dfr.weaken (by intro y hy;simp only [List.mem_cons,List.not_mem_nil,or_false] at *;tauto))

end NearQuarticWires.StagePrint.Header
