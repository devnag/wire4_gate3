import Proof.Quartic.StagePrint.RawGateFormatter
import Proof.Gates.Dispatch.Run

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint.RawBits
open NearCubicGates.Close.Dispatch

/-- `lem:print`, paper/paper.tex: the source formatter initializes its binary arithmetic constants from the cold state. -/
def initializeConstants : St VV := .seq (.op (.inc v1))
  (.seq (.op (.inc v2)) (.op (.inc v2)))

/-- `lem:print` and `prop:time`, paper/paper.tex: the physical source formatter starts with no initialized data oracle. -/
theorem initialize_run (C : Ctx) (hW : 3≤C.Wd) :
    Hs C initializeConstants (a0 (V:=VV)) 5 (fun b=>Cst b ∧ b.cp=0 ∧ b.wq=0 ∧
      b.out=[] ∧ Fr (a0 (V:=VV)) b [v1,v2]) := by
  have hh : 4≤2^C.Wd := (by norm_num :4≤2^3).trans
    (Nat.pow_le_pow_right (by decide) hW)
  unfold initializeConstants
  refine Hx.hs (Hs.then (hs_inc C v1 (a0 (V:=VV)) (by simp [a0];omega))
    (fun b hb n1 hn1=>?_))
  subst hb
  refine Hs.then (hs_inc C v2 _ (by vsimp [a0];omega)) (fun e he n2 hn2=>?_)
  subst he
  refine Hs.last (hs_inc C v2 _ (by vsimp [a0];omega)) (fun f hf n3 hn3=>?_)
  subst hf
  refine ⟨⟨?_,rfl,rfl,rfl,?_⟩,by omega⟩
  · constructor <;> vsimp [a0]
  · exact (Fr.set _ _ (by simp)).trans ((Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp)))

end NearQuarticWires.StagePrint.RawBits
