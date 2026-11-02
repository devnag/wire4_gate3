import Proof.Quartic.StageCert.DeltaMagnitude
import Proof.Wire_3_5.Shared.S0

set_option autoImplicit false

namespace NearQuarticWires.StageCert
open NearCubicGates.Close.Dispatch
open NearCubicWires.WireExponent3_5.Shared

/-- `sec:cells`, paper/paper.tex: the exact integer
mixed difference of the four corner bits in canonical point order. -/
def fourBitDifference (f : Fin 4→Bool) : ℤ := bitZ (f 3)-bitZ (f 1)-bitZ (f 2)+bitZ (f 0)

/-- `sec:cells`, paper/paper.tex: natural signed-count
storage represents the original integer mixed difference without truncation. -/
theorem fourBitDifference_eq (f : Fin 4→Bool) :
    ((f 0).toNat+(f 3).toNat : ℕ)-( ((f 1).toNat+(f 2).toNat : ℕ) : ℤ)=
      fourBitDifference f := by
  have h : ∀b : Bool,((b.toNat : ℕ) : ℤ)=bitZ b := by intro b; cases b <;> rfl
  push_cast
  simp only [h,fourBitDifference]
  ring

/-- `sec:cells` and `def:mask`, paper/paper.tex: the exact signed counts and absolute population contribution
are formed by a single constant-cost arithmetic program. -/
def deltaBits : St VV := .seq deltaCounts absoluteDelta

/-- `sec:cells` and `def:mask`, paper/paper.tex: no negative mixed difference is lost when computing its
absolute contribution to the selected population. -/
theorem deltaBits_run (C : Ctx) (a : DS VV) (hc : Cst a)
    (f : Fin 4→Bool) (hbits : ∀l,a.env (cornerBit l)=(f l).toNat)
    (hfit : 2<2^C.Wd) :
    Hs C deltaBits a 12 (fun z =>
      z.env deltaPositive=(f 0).toNat+(f 3).toNat ∧
      z.env deltaNegative=(f 1).toNat+(f 2).toNat ∧
      z.env deltaMagnitude=(fourBitDifference f).natAbs ∧
      z.cp=a.cp ∧ z.wq=a.wq ∧ z.out=a.out ∧ Cst z ∧
      Fr a z [deltaPositive,deltaNegative,deltaMagnitude]) := by
  have hb : ∀l,a.env (cornerBit l)≤1 := by
    intro l
    rw [hbits]
    cases f l <;> decide
  unfold deltaBits
  refine Hs.seq (t1 := 7) (t2 := 4) (deltaCounts_run C a hc hb hfit) ?_
  rintro b ⟨bp,bn,bc,bw,bo,bconst,bfr⟩
  refine (absoluteDelta_run C b bconst).mono le_rfl ?_
  rintro z ⟨zm,zc,zw,zo,zconst,zfr⟩
  refine ⟨?_,?_,?_,zc.trans bc,zw.trans bw,zo.trans bo,zconst,?_⟩
  · rw [zfr _ (by decide),bp,hbits,hbits]
  · rw [zfr _ (by decide),bn,hbits,hbits]
  · rw [zm,bp,bn,hbits,hbits,hbits,hbits,fourBitDifference_eq]
  · exact (bfr.weaken (by simp)).trans (zfr.weaken (by simp))

end NearQuarticWires.StageCert
