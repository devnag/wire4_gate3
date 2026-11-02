import Proof.Quartic.StageMain.CompactBounds
import Proof.Quartic.StageMain.ParameterGet
import Proof.Quartic.StageGamma.UnaryOutput
import Proof.Gates.Cells.Inv

/-!
# The original main source supplies the field degree

`imp:seed`, paper/paper.tex, and Step 4 of
`sec:algorithm`: the actual parameter record supplies
the field degree. Its unary setup request is printed physically after
reading only the finite preparation prefix of the main source.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open Compact StageLift

def fieldDegreeRegister : Fin VV := 81

def extractActiveDegree : St VV MM := .seq initializeCompact
  (.seq (readParameter 18 fieldDegreeRegister) (StageGamma.unaryOutput fieldDegreeRegister))

def extractActiveCost (c : Call) (p : Cells.Parameters) (witness : List Bool) : ℕ :=
  initializeCost c p witness (compactInput c p witness).length + 7 * p.ellf + 200

theorem scalar_field_degree (p : Cells.Parameters) : (parameterScalars p).getD 18 0 = p.ellf := rfl

theorem extractActiveDegree_run (C : Ctx) (c : Call) (p : Cells.Parameters)
    (witness rest : List Bool) (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip = compactInput c p witness ++ rest)
    (hwidth : (compactInput c p witness).length + 2 ≤ C.Wd) (h64 : 64 ≤ C.Wd)
    (hempty : ∀ store, a.ram store = [] ∧ a.rc store = 0) :
    Hs C extractActiveDegree a (extractActiveCost c p witness) (fun b =>
      b.out = a.out ++ frame (List.replicate p.ellf true)) := by
  obtain ⟨hprefix, hfit, hbits, hprime, hfactor⟩ := compact_decoder_bounds c p witness C.Wd hwidth
  have hell : p.ellf < 2 ^ C.Wd := by
    have hb := hbits p.ellf (by simp [parameterHeadFields, parameterHeadScalars])
    exact (lt_natBitLength p.ellf).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  obtain ⟨b, n, he, hn, hb⟩ := initialize_run C c p (compactInput c p witness).length
    witness rest a hc hin hprefix hfit hbits hwidth ⟨hprime, hfactor⟩
    (fun store _ => hempty store)
  rcases hb with ⟨_hbi, hbdata, _hbl, _hbr, _hbrc, hbrest, hbc, _hbfr⟩
  have hbcur : b.rc parameterStore ≤ 46 := by
    have hh := he.rc_le (by intro store; rw [(hempty store).1, (hempty store).2]; rfl) parameterStore
    rw [hbdata.scalarFields, parameterScalars_length] at hh
    exact hh
  have h18 : 18 < 2 ^ C.Wd := lt_trans (by omega) Nat.lt_two_pow_self
  unfold extractActiveDegree
  refine (Hs.seq (t1 := initializeCost c p witness (compactInput c p witness).length)
    (t2 := 7 * p.ellf + 192)
    (show Hs C initializeCompact a (initializeCost c p witness (compactInput c p witness).length)
      (· = b) from ⟨b, n, he, hn, rfl⟩) ?_).mono
        (by unfold extractActiveCost; omega) (fun _ h => h)
  intro e heq
  subst e
  refine (Hs.seq (t1 := 185) (t2 := 7 * p.ellf + 6)
    ((readParameter_run C p 18 fieldDegreeRegister b hbc hbdata.scalarFields h18 (by decide)).mono
      (by change b.rc parameterStore + 7 * 18 + 13 ≤ 185; omega)
      (fun _ h => h)) ?_).mono (by omega) (fun _ h => h)
  rintro d ⟨hdv, _hdrc, hdrest, _hdc, _hdfr⟩
  have hdegree : d.env fieldDegreeRegister = p.ellf := hdv.trans (scalar_field_degree p)
  refine (StageGamma.unaryOutput_spec C fieldDegreeRegister (by decide) d p.ellf hdegree hell).mono
    le_rfl ?_
  rintro f ⟨hfout, _hfip, _hfkin⟩
  have hdout : d.out = b.out := congrArg (fun t => t.2.1) hdrest
  have hbout : b.out = a.out := congrArg (fun t => t.1) hbrest
  rw [hfout, hdout, hbout]

end NearQuarticWires.StageMain
