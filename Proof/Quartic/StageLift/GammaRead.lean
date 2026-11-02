import Proof.Quartic.StageLift.GammaSplit

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces

/-- `cor:conditional` and Step 3, paper/paper.tex: both original integer-codec fields are read from the
retained Gamma table, rather than supplied as a decoded coefficient. -/
def readGammaInteger (store : Fin MM) : St VV MM :=
  .seq (readMemoryVariable store gammaSignVar) (readMemoryVariable store gammaMagnitudeVar)

/-- `cor:conditional` and Step 3, paper/paper.tex: one real table integer is decoded byte for byte with
binary-length cost and all source data preserved. -/
theorem readGammaInteger_spec (C : Ctx) (store : Fin MM) (bits : List Bool)
    (a : DS VV MM) (hc : Cst a) (ha : a.ram store = bits.map Bool.toNat)
    (z : ℤ) (rest : List Bool)
    (hin : bits.drop (a.rc store) = intWord z ++ rest)
    (hwidth : natBitLength z.natAbs + 2 ≤ C.Wd) (hW : 3 ≤ C.Wd) :
    Hs C (readGammaInteger store) a (30 * natBitLength z.natAbs + 95) (fun b =>
      b.env gammaSignVar = (decide (z < 0)).toNat ∧ b.env gammaMagnitudeVar = z.natAbs ∧
      b.rc store = a.rc store + (intWord z).length ∧
      memorySourceRest store b = memorySourceRest store a ∧ Cst b ∧
      Fr a b (gammaSignVar :: gammaMagnitudeVar :: rdNatT)) := by
  let sign := (decide (z < 0)).toNat
  have hsignBits : natBitLength sign = 1 := by
    by_cases hz : z < 0 <;> simp [sign, hz, natBitLength]
  have hword : intWord z = natWord sign ++ natWord z.natAbs := by
    by_cases hz : z < 0 <;> simp [NearCubicGates.Close.Interfaces.intWord, sign, hz]
  unfold readGammaInteger
  have er := readMemoryVariable_spec C store bits a hc ha gammaSignVar (by decide) (by decide)
    sign (natWord z.natAbs ++ rest) (by simpa only [hword, List.append_assoc] using hin)
    (by rw [hsignBits]; exact hW)
  rw [hsignBits] at er
  refine (Hs.seq (t2 := 30 * natBitLength z.natAbs + 32) er
    fun b ⟨hbs, hbrc, hrest, hbc, hbf⟩ => ?_).mono (by omega) (fun _ h => h)
  have hbram : b.ram = a.ram := congrArg (fun t => t.2.2.1) hrest
  have hbin : bits.drop (b.rc store) = natWord z.natAbs ++ rest := by
    rw [hbrc, ← List.drop_drop, hin, hword, List.append_assoc, List.drop_left]
  refine (readMemoryVariable_spec C store bits b hbc (by rw [hbram]; exact ha)
    gammaMagnitudeVar (by decide) (by decide) z.natAbs rest hbin hwidth).mono le_rfl ?_
  rintro d ⟨hdm, hdrc, hdrest, hdc, hdf⟩
  refine ⟨?_, hdm, ?_, hdrest.trans hrest, hdc, ?_⟩
  · rw [hdf gammaSignVar (by decide)]
    exact hbs
  · rw [hdrc, hbrc, hword, List.length_append]
    omega
  · exact Fr.trans (hbf.weaken (by intro y hy; simp only [List.mem_cons] at hy ⊢; tauto))
      (hdf.weaken (by intro y hy; exact List.mem_cons_of_mem _ hy))

/-- Step 3, `sec:algorithm`, paper/paper.tex: the actual Gamma
table decoder feeds the requested positive/negative split directly. -/
def readSplitGamma (store : Fin MM) : St VV MM :=
  .seq (readGammaInteger store) selectSplitCoefficient

/-- Step 3, `sec:algorithm`, paper/paper.tex: a requested split
weight is obtained from the original Gamma-table bytes with no
separate split-weight data word or sign oracle. -/
theorem readSplitGamma_spec (C : Ctx) (store : Fin MM) (bits : List Bool)
    (a : DS VV MM) (hc : Cst a) (ha : a.ram store = bits.map Bool.toNat)
    (side : Bool) (hpart : a.env partVar = side.toNat) (z : ℤ) (rest : List Bool)
    (hin : bits.drop (a.rc store) = intWord z ++ rest)
    (hwidth : natBitLength z.natAbs + 2 ≤ C.Wd) (hW : 3 ≤ C.Wd) :
    Hs C (readSplitGamma store) a (30 * natBitLength z.natAbs + 98) (fun b =>
      b.env splitCoefficientVar = splitMagnitude side z ∧
      b.rc store = a.rc store + (intWord z).length ∧
      memorySourceRest store b = memorySourceRest store a ∧ Cst b ∧
      Fr a b (splitCoefficientVar :: gammaSignVar :: gammaMagnitudeVar :: rdNatT)) := by
  unfold readSplitGamma
  refine Hs.seq (t2 := 2) (readGammaInteger_spec C store bits a hc ha z rest hin hwidth hW)
    fun b ⟨hbs, hbm, hbrc, hrest, hbc, hbf⟩ => ?_
  refine (selectSplitCoefficient_spec C b hbc side z hbs hbm
    (by rw [hbf partVar (by decide)]; exact hpart)).mono le_rfl ?_
  rintro d ⟨hdv, hdsh, hdc, hdf⟩
  have hs := Same.of_sh hdsh
  refine ⟨hdv, by rw [hs.rc]; exact hbrc, ?_, hdc, ?_⟩
  · simpa only [memorySourceRest, hs.ip, hs.out, hs.ram, hs.rc, hs.kin, hs.kout, hs.kc] using hrest
  · exact Fr.trans (hbf.weaken (by intro y hy; exact List.mem_cons_of_mem _ hy))
      (hdf.weaken (by intro y hy; simp only [List.mem_singleton] at hy; simp [hy]))

end NearQuarticWires.StageLift
