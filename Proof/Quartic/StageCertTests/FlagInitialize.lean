import Proof.Quartic.StageCertTests.FlagArithmetic
import Proof.Quartic.StageRecovery.PacketList

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertTests

open NearCubicGates.Close.Cells
open StageRecovery (countVar)

/-- `sec:algorithm`, paper/paper.tex:
the initial conjunction array is physically filled with true bits. -/
def initializeFlags (store : Fin MM) : St VV MM :=
  forS c0 countVar (.op (.wrM store v1))

/-- `sec:algorithm` and `prop:time`, paper/paper.tex: the exact initial flags are constructed in linear time
from an empty store, preserving every original source and output stream. -/
theorem initializeFlags_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (store : Fin MM) (count : ℕ) (hn : a.env countVar = count)
    (hnfit : count < 2 ^ C.Wd) (hram : a.ram store = []) (hr : a.rc store = 0) :
    Hs C (initializeFlags store) a (5*count+4) (fun b =>
      b.ram store = List.replicate count 1 ∧ b.rc store = count ∧
      (b.ip,b.out,b.kin,b.kout,b.kc) = (a.ip,a.out,a.kin,a.kout,a.kc) ∧
      (∀ m, m ≠ store → b.ram m = a.ram m ∧ b.rc m = a.rc m) ∧
      Cst b ∧ Fr a b [c0]) := by
  let I : ℕ → DS VV MM → Prop := fun k b =>
    b.ram store = List.replicate k 1 ∧ b.rc store = k ∧
    (b.ip,b.out,b.kin,b.kout,b.kc) = (a.ip,a.out,a.kin,a.kout,a.kc) ∧
    (∀ m, m ≠ store → b.ram m = a.ram m ∧ b.rc m = a.rc m) ∧
    Cst b ∧ Fr a b [c0]
  unfold initializeFlags
  refine (forS_spec' c0 countVar (by decide) (.op (.wrM store v1)) a count hnfit I 1
    (fun k b v ⟨hbr,hbc,hbs,hbo,hbz,hbf⟩ => ?_)
    ⟨by simpa using hram,hr,rfl,by intro m _;exact ⟨rfl,rfl⟩,hc,Fr.refl _ _⟩ hn ?_).mono
      (by ring_nf;omega) (fun _ h => h.1)
  · exact ⟨hbr,hbc,hbs,hbo,Cst.of_fr (T := [c0]) hbz (Fr.set _ _ (by decide)) (by decide),
      Fr.trans hbf (Fr.set _ _ (by decide))⟩
  · intro k hk b ⟨hbr,hbc,hbs,hbo,hbz,hbf⟩ hbctr hbn
    have hwrite : b.rc store ≤ (b.ram store).length := by rw [hbr,hbc,List.length_replicate]
    refine (hs_wrM C store v1 b hwrite).mono le_rfl ?_
    rintro d rfl
    refine ⟨⟨?_,?_,hbs,?_,⟨hbz.z,hbz.one,hbz.two⟩,hbf⟩,hbctr,hbn⟩
    · simp only [DS.put,Function.update_self,hbr,hbc,hbz.one,putAt,List.length_replicate,
        lt_self_iff_false,if_false,List.replicate_add,List.replicate_one]
    · simp only [DS.put,Function.update_self,hbc]
    · intro m hm
      simp only [DS.put,Function.update_of_ne hm]
      exact hbo m hm

end NearQuarticWires.StageCertTests
