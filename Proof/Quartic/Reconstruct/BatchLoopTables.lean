import Proof.Quartic.Reconstruct.BatchLoopRun

/-!
# Copying a printed table

Paper: `lem:print`(a), paper/paper.tex: the answer of the word function printing one table is the
list `listWord intWord (printTable r)`. `tableCopier` copies it from the output tape of the called program to the
accumulator (`Codec.copyIntList`, imported from `Proof.Gates.Codec.Copy`) and brings the head of the output tape back
(`tableCopier_exec`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.Reconstruct.Batch

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.RepairOrdinary.Streaming (marks marks_length marks_append)
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat (appendO appendO_st appendO_sh appendO_val appendO_cell)
open NearQuarticWires.Control
open NearCubicGates.Close.Interfaces (listWord)

/-- The copier of a printed table. -/
def tableCopier (p : Program) : WM (cns p.tapeCount) lnr :=
  .seq (NearCubicGates.Close.Codec.copyIntList false (cbank _ p.outputTape) (cT _) cR)
    (halfRewind (cbank _ p.outputTape) (cR 7))

/-- The cost of copying a table. -/
def tableCopyCost (zs : List ℤ) : ℕ :=
  NearCubicGates.Close.Codec.copyListCost zs.length (zs.map fun z => 60 * (NearCubicGates.Close.Interfaces.intWord z).length + 121) +
    1 + ((listWord NearCubicGates.Close.Interfaces.intWord zs).length * 7 + 1)

theorem tableCopier_exec (cap : ℕ) (p : Program) (zs : List ℤ) (σ : WState (cns p.tapeCount) lnr)
    (hO : σ.st (cbank _ p.outputTape) = listWord NearCubicGates.Close.Interfaces.intWord zs)
    (hOh : σ.sh (cbank _ p.outputTape) = 0) (hT : σ.sh (cT _) = (σ.st (cT _)).length) (hR : ∀ i, σ.val (cR i) = 0)
    (hcap : 2 ^ (natBitLength zs.length + 1) + 8 * (listWord NearCubicGates.Close.Interfaces.intWord zs).length + 20 ≤ cap) :
    WExec cap (tableCopier p) σ (appendT σ (cT _) (marks (listWord NearCubicGates.Close.Interfaces.intWord zs)))
      (tableCopyCost zs) := by
  have hOT : cbank p.tapeCount p.outputTape ≠ cT _ := cne _ (by simp [cbank, cT]; omega)
  obtain ⟨hlc1, hlc2⟩ := listWord_count NearCubicGates.Close.Interfaces.intWord zs
    (fun z => by have := natBitLength_le_intWord z; omega)
  have hc0 : 0 ≤ 2 ^ natBitLength zs.length := Nat.zero_le _
  have hpw : 2 ^ (natBitLength zs.length + 1) ≤ cap := by omega
  have hwl : 2 * (listWord NearCubicGates.Close.Interfaces.intWord zs).length + 4 ≤ cap := by omega
  have hz : zs.length ≤ cap := by omega
  have hnb : zs.length + 0 + 6 * natBitLength zs.length + 6 ≤ cap := by omega
  have e1 := NearCubicGates.Close.Codec.copyIntList_spec cap false (cbank _ p.outputTape) (cT _) hOT cR
    (2 * (listWord NearCubicGates.Close.Interfaces.intWord zs).length) hwl zs [] [] σ
    (by rw [hO]; simp [NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.enc])
    hOh hT (fun i _ => hR i) hpw hz (by rw [hR 7]; exact hnb) (by rw [hR 7, marks_length]; omega)
  have h1 : ((appendO σ (cT _) (cR 7) (marks (listWord NearCubicGates.Close.Interfaces.intWord zs))).seth (cbank _ p.outputTape)
      (([] : List Bool).length + NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.stp false *
        (listWord NearCubicGates.Close.Interfaces.intWord zs).length)).val (cR 7) =
      2 * (listWord NearCubicGates.Close.Interfaces.intWord zs).length := by simp [hR 7, marks_length]
  have e2 := halfRewind_spec cap (cbank _ p.outputTape) (cR 7) (listWord NearCubicGates.Close.Interfaces.intWord zs).length _ h1 (by omega)
  refine WExec.cast cap (WExec.seq e1 e2) ?_ (by unfold tableCopyCost; omega)
  refine WState.eq ?_ ?_ ?_ rfl
  · funext q
    by_cases hq : q = cbank p.tapeCount p.outputTape
    · subst hq; simp [appendT, Function.update_of_ne hOT, hOh, NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.stp]
    · by_cases hT' : q = cT _
      · subst hT'; simp [appendT, Function.update_of_ne hOT.symm]
      · simp [appendT, Function.update_of_ne hq, Function.update_of_ne hT']
  · funext q; by_cases hT' : q = cT _
    · subst hT'; simp [appendT]
    · simp [appendT, Function.update_of_ne hT']
  · funext r; by_cases hr : r = cR 7
    · subst hr; simp [appendT, hR 7]
    · simp [appendT, Function.update_of_ne hr]

theorem tableCopier_avoids (p : Program) : WM.Avoids (cOUT p.tapeCount) (tableCopier p) := by
  simp [WM.Avoids, tableCopier, halfRewind, NearCubicGates.Close.Codec.copyIntList, NearCubicGates.Close.Codec.copyList,
    NearCubicGates.Close.Codec.listLoop, NearCubicGates.Close.Codec.copyInt, NearCubicGates.Close.Codec.copyNat,
    NearCubicWires.WireExponent3_5.PrimAsm.CopyNat.copyNatM, NearCubicWires.WireExponent3_5.PrimAsm.CopyNat.copyUnary,
    NearCubicWires.WireExponent3_5.PrimAsm.CopyNat.copyBit, NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.preE,
    NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.readNatM, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.writeNatM,
    NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.emitPair, emitC, WM.fwdC, cbank, cT, cOUT, Fin.ext_iff,
    NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.unaryBody, NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.bitBody,
    NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.addTo, NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.dbl,
    NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.dblLoop, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.bitLenM,
    NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.prefixM, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.payM,
    NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.payBody, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.halveM,
    NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.halveLoop, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.lenLoop,
    NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.onesLoop, NearCubicWires.WireExponent3_5.FinalPass.Hash4.wcopyR,
    NearCubicWires.WireExponent3_5.FinalPass.Hash4.wdup, WM.clear, WM.move]
  all_goals omega

end NearQuarticWires.Reconstruct.Batch
