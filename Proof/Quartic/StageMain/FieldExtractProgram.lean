import Proof.Quartic.StageMain.FieldExtractActive
import Proof.Quartic.StageMain.FieldExtractSizes
import Proof.Gates.Cells.Prelude

/-!
# A uniform field-request extractor on the main source

`imp:seed`, paper/paper.tex, and `prop:time`: the original stage tag determines whether to decode the
selected field degree or emit the fixed one-dimensional request. No
certificate or sample value is supplied separately to this program.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open Compact StageLift

noncomputable def mainFieldDegree (B1 B2 : ℕ) (c : Call) : ℕ :=
  match Program.dispatch B1 B2 c with
  | none => 1
  | some p => p.1.ellf

theorem mainFieldDegree_pos (B1 B2 : ℕ) (c : Call) : 1 ≤ mainFieldDegree B1 B2 c := by
  unfold mainFieldDegree
  split
  · omega
  · rename_i p _
    exact (Cells.prepare_spec _ p.1 p.2).seedParameters.one_le_ell

def extractDefaultDegree : St VV MM :=
  .seq (.op (.emit true)) (.seq (.op (.emit true)) (.op (.emit false)))

theorem extractDefaultDegree_run (C : Ctx) (a : DS VV MM) :
    Hs C extractDefaultDegree a 5 (fun b => b.out = a.out ++ frame [true]) := by
  unfold extractDefaultDegree
  refine Hs.seq (t2 := 3) (hs_emit C true a) ?_
  rintro b rfl
  refine Hs.seq (t2 := 1) (hs_emit C true _) ?_
  rintro b rfl
  refine (hs_emit C false _).mono le_rfl ?_
  rintro b rfl
  simp only [List.append_assoc]
  rfl

def extractFieldBranch : St VV MM := .ite (.eq t0 v1)
  (.seq (.op .bkI) extractActiveDegree) extractDefaultDegree

def extractFieldProgram : St VV MM := .seq initP (.seq (.op (.rdI t0)) extractFieldBranch)

noncomputable def extractFieldSteps (B1 B2 : ℕ) (c : Call) (w : List Bool) : ℕ :=
  match Program.dispatch B1 B2 c with
  | none => 20
  | some p => extractActiveCost c p.1 (Program.witnessPrefix c p.1 w) + 20

theorem extractFieldProgram_run (B1 B2 : ℕ) (c : Call) (w : List Bool) (C : Ctx)
    (hin : C.inp = Program.greedyWord B1 B2 c w)
    (hwidth : C.Wd = (fieldExtractSizes B1 B2).W (leadOnes C.inp)) :
    Hs C extractFieldProgram (a0 : DS VV MM) (extractFieldSteps B1 B2 c w)
      (fun b => b.out = frame (List.replicate (mainFieldDegree B1 B2 c) true)) := by
  have h64 : 64 ≤ C.Wd := by rw [hwidth]; exact fieldExtractSizes_min _ _ _
  have hsmall : 2 < 2 ^ C.Wd := lt_trans (by omega) Nat.lt_two_pow_self
  unfold extractFieldProgram
  cases hd : Program.dispatch B1 B2 c with
  | none =>
    have hinput : C.inp = false :: outputWord (Program.admittedValue B1 B2 Builder.value c w) := by
      rw [hin]
      simp only [Program.greedyWord, Program.stageWord, hd]
    simp only [extractFieldSteps, mainFieldDegree, hd, List.replicate_one]
    refine (Hs.seq (t2 := 8) (initP_spec (C := C) a0 rfl rfl rfl hsmall) ?_).mono
      (by omega) (fun _ h => h)
    rintro a ⟨hc, _hr, _hrc, hip, hout, _hkin, _hkout, _hkc, _hfr⟩
    change a.ip = 0 at hip
    refine Hs.seq (t2 := 6) (readInputBit_spec C t0 a false _ (by rw [hip, List.drop_zero, hinput])) ?_
    rintro b rfl
    unfold extractFieldBranch
    refine Hs.iteF (show t0 ≠ v1 by decide) ?_ ((extractDefaultDegree_run C _).mono le_rfl ?_)
    · simp (config := {decide := true}) [Cnd.eval, DS.set, hc.one]
    · intro d hdout
      simpa only [DS.set_out, hout, a0, List.nil_append] using hdout
  | some p =>
    let witness := Program.witnessPrefix c p.1 w
    let tail := frame (Program.certifiedBits (Program.runCall c p w)) ++
      bitWord (Program.consistentBit (Program.runCall c p w)) ++ frame (Program.runCall c p w).chosenSeed
    have hinput : C.inp = compactInput c p.1 witness ++ tail := by
      rw [hin, greedyWord_compact_layout hd]
      simp only [witness, tail, List.append_assoc]
    have htag : C.inp = true :: (callWord c ++ Program.parametersWord p.1 ++ frame witness ++ tail) := by
      simpa only [compactInput, preparedPrefixWord, List.cons_append, List.append_assoc] using hinput
    have hW : (compactInput c p.1 witness).length + 2 ≤ C.Wd := by
      rw [hwidth, hin]
      exact fieldExtractSizes_active hd w
    simp only [extractFieldSteps, mainFieldDegree, hd]
    refine (Hs.seq (t2 := extractActiveCost c p.1 witness + 5)
      (initP_spec (C := C) a0 rfl rfl rfl hsmall) ?_).mono
      (by dsimp only [witness]; omega) (fun _ h => h)
    rintro a ⟨hc, hr, hrc, hip, hout, _hkin, _hkout, _hkc, _hfr⟩
    change a.ip = 0 at hip
    refine (Hs.seq (t2 := extractActiveCost c p.1 witness + 3)
      (readInputBit_spec C t0 a true _ (by rw [hip, List.drop_zero, htag])) ?_).mono
      (by omega) (fun _ h => h)
    rintro b rfl
    let b : DS VV MM := { a.set t0 1 with ip := a.ip + 1 }
    have hbc : Cst b := Cst.of_fr hc (Fr.set (T := [t0]) a _ (by simp)) (by decide)
    unfold extractFieldBranch
    refine Hs.iteT (show t0 ≠ v1 by decide)
      (by simp (config := {decide := true}) [Cnd.eval, hc.one, DS.set]) ?_
    refine (Hs.seq (t1 := 1) (t2 := extractActiveCost c p.1 witness)
      (Hs.op (OpEx.bkI b (by simp [b])) rfl) ?_).mono (by omega) (fun _ h => h)
    rintro d rfl
    have hdip : b.ip - 1 = 0 := by change a.ip + 1 - 1 = 0; rw [hip]
    refine (extractActiveDegree_run C c p.1 witness tail
      { b with ip := b.ip - 1 } ⟨hbc.z, hbc.one, hbc.two⟩
      (by simp only [hdip, List.drop_zero]; exact hinput)
      hW h64 (by intro store; rw [show ({ b with ip := b.ip - 1 } : DS VV MM).ram = a.ram from rfl,
        show ({ b with ip := b.ip - 1 } : DS VV MM).rc = a.rc from rfl, hr, hrc]; exact ⟨rfl, rfl⟩)).mono
      le_rfl ?_
    intro e heout
    simpa only [b, DS.set_out, hout, a0, List.nil_append] using heout

end NearQuarticWires.StageMain
