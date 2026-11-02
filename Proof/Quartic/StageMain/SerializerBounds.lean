import Proof.Quartic.StageMain.MainSerialization
import Proof.Quartic.StageMain.CompactBounds

/-!
# Binary capacity of the literal main result

Step 4 of `sec:algorithm`, paper/paper.tex,
and `prop:time`: each scalar field has bit length
at most that of the actual output record. Thus the physical printer
requires only the proved word-length bound, with no separate value oracle.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.Controller

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces

theorem finalFields_bitLength {B1 B2 : ℕ} {c : Call} {p : Program.Selected c}
    (hd : Program.dispatch B1 B2 c = some p) (w : List Bool)
    (a : DS VV MM) (hc : Cst a)
    (hnc : a.env certifiedCount = (Program.runCall c p w).certifiedColumns.card)
    (hcon : a.env consistency = (Program.consistentBit (Program.runCall c p w)).toNat)
    (hA : (a.env acceptanceTotal : ℤ) = Program.acceptTotal (Program.runCall c p w))
    (hM : (a.env maskTotal : ℤ) = Program.maskTotal (Program.runCall c p w)) :
    ∀ x ∈ finalFields, natBitLength (x.value c p.1 a) ≤ (Program.mainWord B1 B2 c w).length := by
  intro x hx
  let values := finalFields.map (fun x => x.value c p.1 a)
  have hmem : x.value c p.1 a ∈ values := List.mem_map.mpr ⟨x, hx, rfl⟩
  have hlen := (NearCubicGates.Close.Dispatch.natBitLength_le_len (x.value c p.1 a)).trans
    (Compact.natWord_length_mem _ values hmem)
  have heq : values.flatMap natWord = finalFields.flatMap (fun x => natWord (x.value c p.1 a)) := by
    simp only [values, List.flatMap_map]
  rw [heq] at hlen
  have hword := congrArg List.length (finalFields_word hd w a hc hnc hcon hA hM)
  simp only [List.length_cons] at hword
  omega

theorem serializeMain_actual {B1 B2 : ℕ} (C : Ctx) {c : Call} {p : Program.Selected c}
    (hd : Program.dispatch B1 B2 c = some p) (w : List Bool)
    (a : DS VV MM) (hc : Cst a) (hs : PrintSource c p.1 a)
    (hout : a.out = [])
    (hnc : a.env certifiedCount = (Program.runCall c p w).certifiedColumns.card)
    (hcon : a.env consistency = (Program.consistentBit (Program.runCall c p w)).toNat)
    (hA : (a.env acceptanceTotal : ℤ) = Program.acceptTotal (Program.runCall c p w))
    (hM : (a.env maskTotal : ℤ) = Program.maskTotal (Program.runCall c p w))
    (hindex : 46 < 2 ^ C.Wd)
    (hwidth : (Program.mainWord B1 B2 c w).length + 2 ≤ C.Wd) :
    Hs C serializeMain a
      (3 * (13 * (fieldPrintBound c (Program.mainWord B1 B2 c w).length + 1) + 3) + 2)
      (fun b => b.out = frame (Program.mainWord B1 B2 c w) ∧ PrintSource c p.1 b ∧
      (b.ip, b.ram, b.kin, b.kout, b.kc) = (a.ip, a.ram, a.kin, a.kout, a.kc) ∧
      Cst b ∧ Fr a b sourcePrintScratch) :=
  serializeMain_run C hd w _ a hc hs hout hnc hcon hA hM (by omega) hindex hwidth
    (hwidth.trans_lt Nat.lt_two_pow_self) (finalFields_bitLength hd w a hc hnc hcon hA hM)

end NearQuarticWires.StageMain.Controller
