import Proof.Quartic.StagePrint.RawConstants

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace NearQuarticWires.StagePrint.RawBits
open NearCubicGates.Close.Dispatch
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey

/-- `lem:print`, paper/paper.tex: the original child compiler's six zero working fields are written explicitly. -/
def zeroFields : ℕ→St VV
  | 0 => skipS
  | n+1 => .seq (emitConstantField 0) (zeroFields n)

/-- `lem:print` and `prop:time`, paper/paper.tex: every zero field is initialized, framed and paid for, rather than supplied as precomputed tape contents. -/
theorem zeroFields_run (C : Ctx) (W : ℕ) (hW : W<2^C.Wd) (hctx : 3≤C.Wd) :
    ∀ (n : ℕ) (a : DS VV), Cst a → a.env width=W →
    Hs C (zeroFields n) a (n*(30*W+18)+1) (fun b=>
      b.out=a.out++(List.replicate n (frame (frame (binary W 0)))).flatten ∧
      b.cp=a.cp ∧ b.wq=a.wq ∧ b.env width=W ∧ Cst b ∧ Fr a b scratch) := by
  intro n
  induction n with
  | zero =>
    intro a hc hw
    refine (skip_spec (C:=C) a).mono (by simp) ?_
    rintro b rfl
    have ff : Fr a (a.set vJ 0) scratch:=Fr.set _ _ (by decide)
    exact ⟨by simp,rfl,rfl,by rw [ff width (by decide)];exact hw,
      Cst.of_fr hc ff (by decide) (by rw [ff vPOS (by decide)];exact hc.pos),ff⟩
  | succ n ih =>
    intro a hc hw
    unfold zeroFields
    refine Hs.mono (Hs.seq (t2:=n*(30*W+18)+1)
      (emitConstantField_run C a hc 0 W hw (by positivity) hW hctx)
      (fun b ⟨bo,bp,bw,bwidth,bc,bf⟩=>?_)) (by nlinarith) (fun _ h=>h)
    refine (ih b bc bwidth).mono le_rfl ?_
    rintro e ⟨eo,ep,ew,ewidth,ec,ef⟩
    exact ⟨by rw [eo,bo,List.replicate_succ];simp [List.append_assoc],
      ep.trans bp,ew.trans bw,ewidth,ec,bf.trans ef⟩

end NearQuarticWires.StagePrint.RawBits
