import Proof.Quartic.StageMain.FinalRecord
import Proof.Quartic.StageMain.MarkedOutput
import Proof.Quartic.StageMain.ColumnPass

/-!
# Physical serialization of the exact main-pass result

Step 4 of `sec:algorithm`, paper/paper.tex,
returns the actual totals and Step 5 inputs. The raw record below
is exactly `Program.mainWord`; output markers and the final delimiter
are written by explicit instructions with their full clock charged.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.Controller

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open StageLift SampleCells

theorem finalFields_word {B1 B2 : ℕ} {c : Call} {p : Program.Selected c}
    (hd : Program.dispatch B1 B2 c = some p) (w : List Bool)
    (a : DS VV MM) (hc : Cst a)
    (hnc : a.env certifiedCount = (Program.runCall c p w).certifiedColumns.card)
    (hcon : a.env consistency = (Program.consistentBit (Program.runCall c p w)).toNat)
    (hA : (a.env acceptanceTotal : ℤ) = Program.acceptTotal (Program.runCall c p w))
    (hM : (a.env maskTotal : ℤ) = Program.maskTotal (Program.runCall c p w)) :
    true :: finalFields.flatMap (fun x => natWord (x.value c p.1 a)) =
      Program.mainWord B1 B2 c w := by
  classical
  unfold Program.mainWord Program.stageWord
  rw [hd]
  dsimp only
  rw [← hA, ← hM]
  cases hb : Program.consistentBit (Program.runCall c p w) <;>
    simp [finalFields, FinalField.value, parameterScalars, parameterHeadScalars,
      parameterTailScalars, rationalFields, integerFields, hc.z, hnc, hcon, hb,
      bitWord, Bool.toNat, ratWord, NearCubicGates.Close.Interfaces.intWord, List.append_assoc]

def serializeMain : St VV MM := framedOutputProgram printMainRecord

theorem serializeMain_run {B1 B2 : ℕ} (C : Ctx) {c : Call} {p : Program.Selected c}
    (hd : Program.dispatch B1 B2 c = some p) (w : List Bool)
    (R : ℕ) (a : DS VV MM) (hc : Cst a) (hs : PrintSource c p.1 a)
    (hout : a.out = [])
    (hnc : a.env certifiedCount = (Program.runCall c p w).certifiedColumns.card)
    (hcon : a.env consistency = (Program.consistentBit (Program.runCall c p w)).toNat)
    (hA : (a.env acceptanceTotal : ℤ) = Program.acceptTotal (Program.runCall c p w))
    (hM : (a.env maskTotal : ℤ) = Program.maskTotal (Program.runCall c p w))
    (hW : 2 ≤ C.Wd) (hindex : 46 < 2 ^ C.Wd)
    (hwidth : R + 2 ≤ C.Wd) (hfit : R + 2 < 2 ^ C.Wd)
    (hbits : ∀ x ∈ finalFields, natBitLength (x.value c p.1 a) ≤ R) :
    Hs C serializeMain a (3 * (13 * (fieldPrintBound c R + 1) + 3) + 2) (fun b =>
      b.out = frame (Program.mainWord B1 B2 c w) ∧ PrintSource c p.1 b ∧
      (b.ip, b.ram, b.kin, b.kout, b.kc) = (a.ip, a.ram, a.kin, a.kout, a.kc) ∧
      Cst b ∧ Fr a b sourcePrintScratch) := by
  obtain ⟨b, n, he, hn, hbo, hbs, hbrest, hbc, hbfr⟩ :=
    printMainRecord_run C c p.1 R a hc hs hW hindex hwidth hfit hbits
  have hword : b.out = Program.mainWord B1 B2 c w := by
    rw [hbo, hout, List.nil_append]
    exact finalFields_word hd w a hc hnc hcon hA hM
  have hmarked : markOutputState a = a := by
    unfold markOutputState
    simp only [hout, List.flatMap_nil]
    rw [← hout]
  have hf := framedOutput_run he
  rw [hmarked] at hf
  exact ⟨{ b with out := frame b.out }, 3 * n + 2, hf, by omega,
    congrArg frame hword, ⟨hbs.call, hbs.parameters, hbs.callCursor, hbs.parameterCursor⟩,
    hbrest, ⟨hbc.z, hbc.one, hbc.two⟩, hbfr⟩

end NearQuarticWires.StageMain.Controller
