import Proof.Quartic.StageCertificateControl.CountCall
import Proof.Quartic.StageCertificateControl.CountCost
import Proof.Gates.Codec.Unframe
import Proof.Quartic.StagePrint.PoolAvoids

/-!
# The whole-test count occupies the reusable native bank first

Paper: Step 2 of `sec:algorithm`, paper/paper.tex,
and `prop:time`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicGates.Close NearCubicGates.Close.Codec NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.WorkerArith (inTape)
open NearQuarticWires.Control

/-- `prop:time`, paper/paper.tex: the count
program uses an initial portion of the native program's physical bank. -/
def countBankSite (p q : Program) (hq : q.tapeCount≤p.tapeCount) : Site q (p.tapeCount+5) 16 where
  bank j := StagePrint.poolBank p.tapeCount ⟨j.val,lt_of_lt_of_le j.isLt hq⟩
  tally := ⟨2,by omega⟩
  guard := ⟨3,by omega⟩
  ruler := ⟨4,by omega⟩
  regs := StagePrint.poolSiteRegs
  bank_inj := by
    intro i j h
    apply Fin.ext
    have hh := congrArg Fin.val h
    change 5+i.val=5+j.val at hh
    omega
  tally_ne := by intro j h;have hh := congrArg Fin.val h;change 5+j.val=2 at hh;omega
  guard_ne := by intro j h;have hh := congrArg Fin.val h;change 5+j.val=3 at hh;omega
  ruler_ne := by intro j h;have hh := congrArg Fin.val h;change 5+j.val=4 at hh;omega
  tally_guard := by intro h;have hh := congrArg Fin.val h;change 2=3 at hh;omega
  tally_ruler := by intro h;have hh := congrArg Fin.val h;change 2=4 at hh;omega
  guard_ruler := by intro h;have hh := congrArg Fin.val h;change 3=4 at hh;omega

/-- `prop:time`, paper/paper.tex: count-bank
input is distinct from the original preparation and from the fresh output. -/
theorem countBankSite_input_ne (p q : Program) (hq : q.tapeCount≤p.tapeCount) :
    (countBankSite p q hq).input≠StagePrint.poolSource p ∧
    (countBankSite p q hq).input≠StagePrint.poolFinal p := by
  constructor
  · intro h;have hh := congrArg Fin.val h
    change 5+(inTape q).val=0 at hh
    omega
  · intro h;have hh := congrArg Fin.val h
    change 5+(inTape q).val=p.tapeCount+5 at hh
    have hi := (inTape q).isLt
    omega

/-- `sec:algorithm` and `prop:time`, paper/paper.tex: the literal preparation is copied once into
the count bank, its true count is read, and every count-bank cell is erased. -/
noncomputable def poolCountProgram (p q : Program) (hq : q.tapeCount≤p.tapeCount) :
    WMX (p.tapeCount+5) 16 :=
  .seq (.wm (copyRW (StagePrint.poolSource p) (countBankSite p q hq).input 8 9 10))
    (countCallProgram (countBankSite p q hq))

end NearQuarticWires.StageCertificateControl
