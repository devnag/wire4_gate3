import Proof.Gates.Cells.Kit

/-!
# Measuring the physically scanned call prefix

`prop:time`, paper/paper.tex: every self-delimiting
natural field contributes its actual encoded bit length to a retained
counter. This counter bounds subsequent copies of the finite call
without including the following certificate or table stream.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.CallSkip

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces

def lengthCounter : Fin VV := 108

def countNatWord : St VV MM := .seq (.op (.add lengthCounter t4))
  (.seq (.op (.add lengthCounter t4)) (.op (.inc lengthCounter)))

theorem countNatWord_run (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (hcap : a.env lengthCounter + 2 * a.env t4 + 1 < 2 ^ C.Wd) :
    Hs C countNatWord a 5 (fun b =>
      b.env lengthCounter = a.env lengthCounter + 2 * a.env t4 + 1 ∧
      Same a b ∧ Cst b ∧ Fr a b [lengthCounter]) := by
  refine Hs.seq (t1 := 1) (t2 := 3)
    (hs_add C lengthCounter t4 a (by decide) (by omega)) ?_
  rintro b rfl
  have ht : (a.set lengthCounter (a.env lengthCounter + a.env t4)).env t4 = a.env t4 :=
    DS.set_env_ne _ _ (by decide)
  refine Hs.seq (t1 := 1) (t2 := 1)
    (hs_add C lengthCounter t4 _ (by decide) (by simp only [DS.set_env_self, ht]; omega)) ?_
  rintro b rfl
  refine (hs_inc C lengthCounter _ (by simp only [DS.set_env_self, ht]; omega)).mono le_rfl ?_
  rintro b rfl
  refine ⟨by simp only [DS.set_env_self, ht]; omega,
    (Same.set _ _ _).trans ((Same.set _ _ _).trans (Same.set _ _ _)), ?_, ?_⟩
  · exact Cst.of_fr hc ((Fr.set a _ (by simp : lengthCounter ∈ [lengthCounter])).trans
      ((Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp)))) (by decide)
  · exact (Fr.set a _ (by simp)).trans ((Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp)))

def scanNat : St VV MM := .seq rdNatI countNatWord

def atomScratch : List (Fin VV) := lengthCounter :: rdNatT

theorem scanNat_read_run (C : Ctx) (a : DS VV MM) (hc : Cst a) (v : ℕ) (rest : List Bool)
    (hin : C.inp.drop a.ip = natWord v ++ rest) (hW : natBitLength v + 2 ≤ C.Wd)
    (hcap : a.env lengthCounter + (natWord v).length < 2 ^ C.Wd) :
    Hs C scanNat a (30 * natBitLength v + 36) (fun b =>
      b.env t3 = v ∧ b.env t4 = natBitLength v ∧
      b.ip = a.ip + (natWord v).length ∧
      (b.out, b.ram, b.rc, b.kin, b.kout, b.kc) =
        (a.out, a.ram, a.rc, a.kin, a.kout, a.kc) ∧
      Cst b ∧ Fr a b atomScratch ∧
      b.env lengthCounter = a.env lengthCounter + (natWord v).length) := by
  refine Hs.mono (Hs.seq (t1 := 30 * natBitLength v + 30) (t2 := 5)
    (rdNatI_spec a hc v rest hin hW) ?_) (by omega) (fun _ h => h)
  intro b ⟨hbn, hbl, hbi, hrest, hfr⟩
  have hbc := cst_fr hc hfr
  have hlen : b.env lengthCounter = a.env lengthCounter := hfr _ (by decide)
  refine (countNatWord_run C b hbc (by rw [hlen, hbl]; simpa [natWord_length, Nat.add_assoc] using hcap)).mono le_rfl ?_
  intro d ⟨hdn, hsame, hdc, hdfr⟩
  refine ⟨(hdfr t3 (by decide)).trans hbn, (hdfr t4 (by decide)).trans hbl,
    hsame.ip.trans hbi, ?_, hdc, ?_, ?_⟩
  · rw [hsame.out, hsame.ram, hsame.rc, hsame.kin, hsame.kout, hsame.kc]
    exact hrest
  · exact (hfr.weaken (fun _ hx => List.mem_cons_of_mem _ hx)).trans
      (hdfr.weaken (by simp))
  · rw [hdn, hlen, hbl, natWord_length]
    omega

end NearQuarticWires.StageMain.CallSkip
