import Proof.Quartic.StageColumns.Bit
import Proof.Gates.CounterMachine.CellTablesLem
import Proof.Wire_3_5.FinalPassWordMap

set_option autoImplicit false

namespace NearQuarticWires.StageColumns

open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicGates.Close.Cells

def outputRest (a : DS VV MM) := (a.ip, a.ram, a.rc, a.kin, a.kout, a.kc)

theorem outputRest_of_sh {a b : DS VV MM} (h : b.sh = a.sh) : outputRest b = outputRest a := by
  have hs := Same.of_sh h
  simp only [outputRest, hs.ip, hs.ram, hs.rc, hs.kin, hs.kout, hs.kc]

def pairProgram : St VV MM :=
  .seq (.op (.emit true))
    (.ite (.eq result v1) (.op (.emit true)) (.op (.emit false)))

/-- `lem:print`, paper/paper.tex: each computed
column bit is emitted with its actual inner-field marker. -/
theorem pairProgram_run (C : Ctx) (a : DS VV MM) (hc : Cst a) (bit : Bool)
    (hb : a.env result = bit.toNat) :
    Hs C pairProgram a 4 (fun b => b = {a with out := a.out ++ [true, bit]}) := by
  unfold pairProgram
  refine Hs.seq (t1 := 1) (t2 := 2) (hs_emit C true a) ?_
  rintro b rfl
  cases bit with
  | false =>
    refine Hs.iteF (show result ≠ v1 by decide) (by simp [Cnd.eval, hb, hc.one]) ?_
    refine (hs_emit C false _).mono le_rfl ?_
    rintro b rfl
    simp only [List.append_assoc]
    rfl
  | true =>
    refine Hs.iteT (show result ≠ v1 by decide) (by simp [Cnd.eval, hb, hc.one]) ?_
    refine (hs_emit C true _).mono le_rfl ?_
    rintro b rfl
    simp only [List.append_assoc]
    rfl

def emitBitProgram : St VV MM := .seq bitProgram pairProgram

/-- `imp:partition` and `lem:print`, paper/paper.tex: compute and serialize the original canonical column bit,
retaining the actual source metadata and both enumeration indices. -/
theorem emitBitProgram_run (C : Ctx) (a : DS VV MM) (P : StarParams) (j p : ℕ)
    (hi : BitInputs a P j p) (hj : j < PrimT.C4Geo.dRow P)
    (hwidth : P.n + 4 ≤ C.Wd) :
    Hs C emitBitProgram a (bitClock P + 5) (fun b =>
      b.out = a.out ++ [true, PrimT.C4Geo.colBit P j p] ∧
      outputRest b = outputRest a ∧ Fr a b bitScratch) := by
  unfold emitBitProgram
  refine Hs.seq (bitProgram_run C a P j p hi hj hwidth) ?_
  rintro b ⟨hbv, hbsh, hbfr⟩
  have hbc : Cst b := hi.constants.of_fr hbfr (by decide)
  refine (pairProgram_run C b hbc (PrimT.C4Geo.colBit P j p) hbv).mono le_rfl ?_
  rintro c rfl
  exact ⟨by rw [(Same.of_sh hbsh).out], by change outputRest b = outputRest a; exact outputRest_of_sh hbsh, hbfr⟩

end NearQuarticWires.StageColumns
