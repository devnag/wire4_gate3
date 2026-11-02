import Proof.Gates.Cells.Loop
import Proof.Quartic.Algorithm.Parameters

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint.Header
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells

/-- `imp:partition` and `lem:print`, paper/paper.tex: the exact low-first value of the retained witness prefix. -/
def binaryPrefix (bits : List Bool) (n : ℕ) : ℕ :=
  ∑ i∈Finset.range n,if bits.getD i false then 2^i else 0

/-- `imp:partition`, paper/paper.tex: the next physical witness bit has its original binary positional weight. -/
theorem binaryPrefix_succ (bits : List Bool) (n : ℕ) :
    binaryPrefix bits (n+1)=binaryPrefix bits n+(bits.getD n false).toNat*2^n := by
  rw [binaryPrefix,Finset.sum_range_succ]
  cases bits.getD n false <;> simp [binaryPrefix]

/-- `imp:partition`, paper/paper.tex: every finite witness prefix is already in its canonical residue range. -/
theorem binaryPrefix_lt (bits : List Bool) : ∀n,binaryPrefix bits n<2^n
  | 0=>by simp [binaryPrefix]
  | n+1=>by
    rw [binaryPrefix_succ,pow_succ]
    have hh:=binaryPrefix_lt bits n
    have hb : (bits.getD n false).toNat≤1 := by cases bits.getD n false <;> decide
    have:=Nat.mul_le_mul_right (2^n) hb
    omega

/-- `imp:partition` and `lem:print`, paper/paper.tex: the runtime translation accumulator and positional weight are separate from all parameter-reader slots. -/
def translation : Fin VV:=80
def power : Fin VV:=81
def count : Fin VV:=82
def index : Fin VV:=83

/-- `imp:partition` and `lem:print`, paper/paper.tex: one retained witness bit is fetched from actual memory and added with its binary weight. -/
def translationBody (store : Fin MM) : St VV MM :=
  .seq (fetch store index t1)
    (.seq (.op (.mul t1 power t3))
      (.seq (.op (.add translation t3)) (.op (.shl power))))

/-- `imp:partition` and `lem:print`, paper/paper.tex: one memory-prefix step changes only its declared accumulator and memory-access scratch slots. -/
def translationScratch : List (Fin VV):=[c0,vJ,t1,t3,translation,power]

/-- `imp:partition` and `lem:print`, paper/paper.tex: the actual memory operation computes one exact translation bit without a supplied syndrome number. -/
theorem translationBody_run (C : Ctx) (store : Fin MM) (bits : List Bool)
    (k : ℕ) (a : DS VV MM) (hc : Cst a)
    (hmem : a.ram store=bits.map Bool.toNat) (hk : k<bits.length)
    (hi : a.env index=k) (hpower : a.env power=2^k)
    (hvalue : a.env translation=binaryPrefix bits k)
    (hcap : 2^(k+1)<2^C.Wd) :
    Hs C (translationBody store) a (a.rc store+5*k+16) (fun b=>
      b.env translation=binaryPrefix bits (k+1) ∧ b.env power=2^(k+1) ∧
      b.ip=a.ip ∧ b.out=a.out ∧ b.ram=a.ram ∧
      b.rc=Function.update a.rc store (k+1) ∧
      (b.kin,b.kout,b.kc)=(a.kin,a.kout,a.kc) ∧ Cst b ∧ Fr a b translationScratch) := by
  have hfetch:=fetch_spec (C:=C) store index t1 (by decide) (by decide) a
    (by rw [hi,hmem,List.length_map];exact hk)
    (by rw [hi];have:=Nat.lt_two_pow_self (n:=k);have:=Nat.one_le_two_pow (n:=k);rw [pow_succ] at hcap;omega)
  unfold translationBody
  refine (Hs.seq (t2:=5) hfetch ?_).mono (by rw [hi];omega) (fun _ h=>h)
  rintro b ⟨bv,bi,bo,br,brc,bkin,bkout,bkc,bfr⟩
  have bc : Cst b:=Cst.of_fr hc bfr (by decide)
  have bpow : b.env power=2^k := by rw [bfr power (by decide)];exact hpower
  have bval : b.env translation=binaryPrefix bits k := by rw [bfr translation (by decide)];exact hvalue
  have bbit : b.env t1=(bits.getD k false).toNat := by
    rw [bv,hi,hmem]
    change (bits.map Bool.toNat).getD k (Bool.toNat false)=_
    rw [List.getD_map]
  have hbit : (bits.getD k false).toNat≤1 := by cases bits.getD k false <;> decide
  have hsmall : binaryPrefix bits k+(bits.getD k false).toNat*2^k<2^C.Wd := by
    rw [←binaryPrefix_succ]
    exact (binaryPrefix_lt bits (k+1)).trans hcap
  refine Hs.seq (t2:=3) (hs_mul C t1 power t3 b (by decide) (by decide) (by decide) ?_) ?_
  · rw [bbit,bpow]
    omega
  rintro d rfl
  let d:=b.set t3 (b.env t1*b.env power)
  have bval80 : b.env 80=binaryPrefix bits k := bval
  have bpow81 : b.env 81=2^k := bpow
  have ed:=hs_add C translation t3 d (by decide) (by
    simpa (config:={decide:=true}) [d,translation,power,t3,bval80,bbit,bpow81] using hsmall)
  refine Hs.seq (t2:=1) ed ?_
  rintro e rfl
  let e:=d.set translation (d.env translation+d.env t3)
  have ep : e.env power=2^k := by simpa (config:={decide:=true}) [e,d,translation,power,t3] using bpow
  refine (hs_shl C power e (by rw [ep];rw [pow_succ] at hcap;simpa [Nat.mul_comm] using hcap)).mono le_rfl ?_
  rintro f rfl
  have fr : Fr b (e.set power (2*e.env power)) [t3,translation,power] := by
    exact (Fr.set b _ (by simp)).trans
      ((Fr.set d _ (by simp)).trans (Fr.set e _ (by simp)))
  refine ⟨?_,?_,bi,bo,br,?_,Prod.ext bkin (Prod.ext bkout bkc),?_,?_⟩
  · simpa (config:={decide:=true}) [e,d,translation,power,t3,binaryPrefix_succ] using
      congrArg₂ (fun x y : ℕ=>x+y) bval (congrArg₂ (fun x y : ℕ=>x*y) bbit bpow)
  · simp [ep,pow_succ,Nat.mul_comm]
  · simpa [e,d,hi] using brc
  · exact Cst.of_fr bc fr (by decide)
  · exact (bfr.weaken (by simp [translationScratch])).trans (fr.weaken (by simp [translationScratch]))

end NearQuarticWires.StagePrint.Header
