import Proof.Gates.Cells.Kit

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicGates.Close.Cells

/-- `lem:print`, paper/paper.tex: retained source
bits occupy an actual record store, with only its cursor excluded
from the invariant remainder of the machine state. -/
def memorySourceRest (store : Fin MM) (a : DS VV MM) :=
  (a.ip, a.out, a.ram, Function.update a.rc store 0, a.kin, a.kout, a.kc)

/-- `sec:algorithm` and `lem:print`, paper/paper.tex: a framed word already retained by real record writes
is read by the standard binary field decoder through physical memory
reads, with no decoded-bit or arithmetic-value oracle. -/
def memorySource (C : Ctx) (store : Fin MM) (bits : List Bool) :
    Src C (ℕ × List Bool × (Fin MM → List ℕ) × (Fin MM → ℕ) × List Bool × List Bool × ℕ) where
  word := bits
  pos a := a.rc store
  rest := memorySourceRest store
  op x := .rdM store x
  nxt a x := (a.set x (bitOf bits (a.rc store))).adv store
  ok a := a.ram store = bits.map Bool.toNat
  spec a x ha hp := by
    have hread : (a.ram store).getD (a.rc store) 0 = bitOf bits (a.rc store) := by
      rw [ha]
      rw [List.getD_eq_getElem _ _ (by simpa using hp)]
      simp only [List.getElem_map]
      rw [bitOf, List.getD_eq_getElem _ _ hp]
    simpa only [hread] using OpEx.rdM (C := C) store x a (by simpa [ha] using hp)
  env a x _ := by
    rfl
  posn a x := by simp [DS.adv, DS.set]
  restn a x := by
    simp [memorySourceRest, DS.adv, DS.set, Function.update_idem]
  pos_set a y v := rfl
  rest_set a y v := rfl
  ok_of a b hr ha := by
    have hm : b.ram = a.ram := congrArg (fun t => t.2.2.1) hr
    rw [hm]
    exact ha

/-- `lem:print`, paper/paper.tex: natural fields
inside the retained witness or Gamma stream are decoded by actual
record reads with the unchanged binary natural-number algorithm. -/
def readMemoryNatural (store : Fin MM) : St VV MM := rdNat (fun x => .rdM store x)

/-- `lem:print`, paper/paper.tex: a retained field
is read exactly once from its real byte records, preserves the original
input cursor and advances only the retained-source cursor. -/
theorem readMemoryNatural_spec (C : Ctx) (store : Fin MM) (bits : List Bool)
    (a : DS VV MM) (hc : Cst a) (ha : a.ram store = bits.map Bool.toNat)
    (value : ℕ) (rest : List Bool)
    (hin : bits.drop (a.rc store) = NearCubicWires.RepairRepresentation.natWord value ++ rest)
    (hwidth : NearCubicWires.natBitLength value + 2 ≤ C.Wd) :
    Hs C (readMemoryNatural store) a (30 * NearCubicWires.natBitLength value + 30) (fun b =>
      b.env t3 = value ∧ b.env t4 = NearCubicWires.natBitLength value ∧
      b.rc store = a.rc store + (NearCubicWires.RepairRepresentation.natWord value).length ∧
      memorySourceRest store b = memorySourceRest store a ∧ Fr a b rdNatT) :=
  rdNat_spec (memorySource C store bits) a hc ha value rest hin hwidth

end NearQuarticWires.StageLift
