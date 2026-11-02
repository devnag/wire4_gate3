import Proof.Quartic.StagePrint.RawSigned

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false

namespace NearQuarticWires.StagePrint.RawBits
open NearCubicGates.Close.Dispatch
open NearCubicGates.Close.WordPrograms.SInt (encS)

/-- `imp:disjoint` and `lem:print`, paper/paper.tex: the inclusive original threshold becomes the strict target threshold minus one. -/
theorem predecessor_code (z : ℤ) : encS (z-1)=
    if z<0 then encS z+2 else if z=0 then 3 else encS z-2 := by
  cases z with
  | ofNat n =>
    cases n with
    | zero => decide
    | succ n =>
      have hh : Int.ofNat (n+1)-1=Int.ofNat n := by
        simp only [Int.ofNat_eq_natCast];omega
      rw [hh]
      simp [encS,Int.ofNat_eq_natCast]
      have hpos : ¬((n:ℤ)+1<0) := by omega
      have hne : ¬((n:ℤ)+1=0) := by omega
      have ha : ((n:ℤ)+1).natAbs=n+1 := rfl
      simp only [hpos,hne,if_false,ha]
      omega
  | negSucc n =>
    have hh : Int.negSucc n-1=Int.negSucc (n+1) := by omega
    rw [hh]
    simp only [encS,Int.natAbs_negSucc]
    split_ifs <;> omega

/-- `lem:print`, paper/paper.tex: a ready sign/magnitude pair is converted to the unchanged signed code. -/
def encodeReady : St VV := .seq (.op (.mul t3 v2 value)) (.op (.add value t8))

/-- `lem:print`, paper/paper.tex: the signed-code arithmetic preserves all input cursors and original fields. -/
theorem encodeReady_run (C : Ctx) (a : DS VV) (hc : Cst a) (z : ℤ)
    (hm : a.env t3=z.natAbs) (hs : a.env t8=if z<0 then 1 else 0)
    (hfit : encS z<2^C.Wd) :
    Hs C encodeReady a 3 (fun b=>b.env value=encS z ∧
      b.cp=a.cp ∧ b.wq=a.wq ∧ b.out=a.out ∧ Cst b ∧ Fr a b [value]) := by
  unfold encodeReady
  refine Hs.mono (Hs.seq (t2:=1) (hs_mul C t3 v2 value a (by decide) (by decide) (by decide)
    (by rw [hm,hc.two];unfold encS at hfit;omega)) (fun b hb=>?_)) le_rfl (fun _ h=>h)
  subst hb
  refine (hs_add C value t8 (a.set value (a.env t3*a.env v2)) (by decide)
    (by vsimp [hm,hc.two,hs];simpa [encS,Nat.mul_comm] using hfit)).mono le_rfl ?_
  rintro b rfl
  have ff : Fr a ((a.set value (a.env t3*a.env v2)).set value
      ((a.set value (a.env t3*a.env v2)).env value+
        (a.set value (a.env t3*a.env v2)).env t8)) [value] :=
    (Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp))
  refine ⟨?_,rfl,rfl,rfl,Cst.of_fr hc ff (by decide)
    (by rw [ff vPOS (by decide)];exact hc.pos),ff⟩
  vsimp [encS,hm,hc.two,hs,Nat.mul_comm]

/-- `imp:disjoint` and `lem:print`, paper/paper.tex: subtract one from the signed source threshold without changing any original weight. -/
def predecessorReady : St VV :=
  .ite (.eq t8 v1) (.op (.add value v2))
    (.ite (.eq t3 vZ) (setK value 3) (.op (.sub value v2)))

/-- `imp:disjoint` and `lem:print`, paper/paper.tex: the physical predecessor conversion is exact also at zero and negative thresholds. -/
theorem predecessorReady_run (C : Ctx) (a : DS VV) (hc : Cst a) (z : ℤ)
    (hm : a.env t3=z.natAbs) (hs : a.env t8=if z<0 then 1 else 0)
    (hv : a.env value=encS z) (hfit : encS z+3<2^C.Wd) :
    Hs C predecessorReady a 12 (fun b=>b.env value=encS (z-1) ∧
      b.cp=a.cp ∧ b.wq=a.wq ∧ b.out=a.out ∧ Cst b ∧ Fr a b [value,vJ]) := by
  unfold predecessorReady
  by_cases hz : z<0
  · refine Hs.iteT (show t8≠v1 from by decide) (by simp [Cnd.eval,hs,hz,hc.one]) ?_
    refine (hs_add C value v2 a (by decide) (by rw [hv,hc.two];omega)).mono (by omega) ?_
    rintro b rfl
    have ff : Fr a (a.set value (a.env value+a.env v2)) [value,vJ] := Fr.set _ _ (by simp)
    exact ⟨by simp [hv,hc.two,predecessor_code,hz],rfl,rfl,rfl,
      Cst.of_fr hc ff (by decide) (by rw [ff vPOS (by decide)];exact hc.pos),ff⟩
  · refine Hs.iteF (show t8≠v1 from by decide) (by simp [Cnd.eval,hs,hz,hc.one]) ?_
    by_cases hzero : z=0
    · subst hzero
      refine Hs.iteT (show t3≠vZ from by decide) (by simp [Cnd.eval,hm,hc.z]) ?_
      refine (setK_spec value (by decide) 3 a (by have : encS 0=0:=rfl;omega)).mono (by omega) ?_
      rintro b ⟨bv,bp,bw,bo,bf⟩
      exact ⟨by simpa [encS] using bv,bp,bw,bo,
        Cst.of_fr hc bf (by decide) (by rw [bf vPOS (by decide),hc.pos,bp]),bf⟩
    · have habs : z.natAbs≠0 := fun h=>hzero (Int.natAbs_eq_zero.mp h)
      refine Hs.iteF (show t3≠vZ from by decide) (by simp [Cnd.eval,hm,hc.z,habs]) ?_
      refine (hs_sub C value v2 a (by decide)
        (by rw [hv,hc.two];unfold encS;split_ifs <;>omega)).mono (by omega) ?_
      rintro b rfl
      have ff : Fr a (a.set value (a.env value-a.env v2)) [value,vJ] := Fr.set _ _ (by simp)
      exact ⟨by simp [hv,hc.two,predecessor_code,hz,hzero],rfl,rfl,rfl,
        Cst.of_fr hc ff (by decide) (by rw [ff vPOS (by decide)];exact hc.pos),ff⟩

end NearQuarticWires.StagePrint.RawBits
