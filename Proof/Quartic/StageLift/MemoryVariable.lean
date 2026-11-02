import Proof.Quartic.StageLift.MemorySource

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells

/-- `lem:print`, paper/paper.tex: retain a decoded
natural field from the actual stored witness or Gamma source. -/
def readMemoryVariable (store : Fin MM) (target : Fin VV) : St VV MM :=
  .seq (readMemoryNatural store) (.op (.copy target t3))

/-- `lem:print`, paper/paper.tex: stored input fields
are decoded with their exact binary lengths and retained without
changing the original input or any coefficient/source record data. -/
theorem readMemoryVariable_spec (C : Ctx) (store : Fin MM) (bits : List Bool)
    (a : DS VV MM) (hc : Cst a) (ha : a.ram store = bits.map Bool.toNat)
    (target : Fin VV) (htarget : target ∉ rdNatT)
    (hconst : target ≠ vZ ∧ target ≠ v1 ∧ target ≠ v2)
    (value : ℕ) (rest : List Bool)
    (hin : bits.drop (a.rc store) = natWord value ++ rest)
    (hwidth : natBitLength value + 2 ≤ C.Wd) :
    Hs C (readMemoryVariable store target) a (30 * natBitLength value + 32) (fun b =>
      b.env target = value ∧ b.rc store = a.rc store + (natWord value).length ∧
      memorySourceRest store b = memorySourceRest store a ∧ Cst b ∧ Fr a b (target :: rdNatT)) := by
  have hne : target ≠ t3 := by intro h; exact htarget (h ▸ by decide)
  unfold readMemoryVariable
  refine Hs.seq (t2 := 1) (readMemoryNatural_spec C store bits a hc ha value rest hin hwidth)
    fun b ⟨hbv, _hbl, hbrc, hrest, hbf⟩ => ?_
  refine (hs_copy C target t3 b hne).mono le_rfl ?_
  rintro d rfl
  have hbc : Cst b := cst_fr hc hbf
  exact ⟨by simpa only [DS.set_env_self] using hbv, hbrc, hrest,
    Cst.of_fr (T := [target]) hbc (Fr.set b _ (by simp))
      (by simpa only [List.mem_singleton, not_or] using
        ⟨Ne.symm hconst.1, Ne.symm hconst.2.1, Ne.symm hconst.2.2⟩),
    Fr.trans (hbf.weaken (by intro y hy; exact List.mem_cons_of_mem _ hy))
      (Fr.set b _ (by simp))⟩

end NearQuarticWires.StageLift
