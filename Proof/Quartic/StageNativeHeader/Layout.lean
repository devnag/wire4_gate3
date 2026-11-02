import Proof.Quartic.StagePrint.DownstreamTargets
import Proof.Quartic.StagePrint.CallAppend
import Proof.Quartic.StagePrint.NativeCutCount
import Proof.Quartic.StageColumns.Cost
import Proof.Quartic.Control.Write
import Proof.Quartic.Control.Frame
import Proof.Quartic.Control.Head
import Proof.Wire_3_5.PrimAsmParseNat

/-!
# The layout of the native header printer

Paper: `lem:print`, paper/paper.tex.

The printer is one word program on the streams `sIN` (the framed input), `sOUT`, the accumulator `sACC` of the
marked output, the raw cut stream `sX`, the column field `sY` and its copy `sY2`, three scratch streams for numbers,
the ruler, tally and guard of one call site, a dummy target of the cut count, and the bank of the column printer
`StageColumns.columnWordFunction`. `emitList` appends a fixed list of bits; `deep3` is one bit at depth three.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageNativeHeader

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat (appendO appendO_st appendO_sh appendO_val appendO_cell
  appendO_append appendO_nil appendO_setv)
open NearQuarticWires.Control

/-- The column printer. -/
noncomputable abbrev colWF := NearQuarticWires.StageColumns.columnWordFunction

/-- The number of tapes of the column printer. -/
noncomputable abbrev tc : ℕ := colWF.program.tapeCount

/-- The number of streams minus one. -/
noncomputable abbrev hns : ℕ := 12 + tc

/-- The number of registers. -/
abbrev hnr : ℕ := 56

/-- A named stream. -/
def strm (k : ℕ) (h : k ≤ 12) : Fin (hns + 1) := ⟨k, by simp only [hns]; omega⟩

/-- The framed input. -/
noncomputable def sIN : Fin (hns + 1) := strm 0 (by decide)
/-- The output. -/
noncomputable def sOUT : Fin (hns + 1) := strm 1 (by decide)
/-- The accumulator of the marked output. -/
noncomputable def sACC : Fin (hns + 1) := strm 2 (by decide)
/-- The raw cut stream. -/
noncomputable def sX : Fin (hns + 1) := strm 3 (by decide)
/-- The column field. -/
noncomputable def sY : Fin (hns + 1) := strm 4 (by decide)
/-- A copy of the column field. -/
noncomputable def sY2 : Fin (hns + 1) := strm 5 (by decide)
/-- The number `d`. -/
noncomputable def sZd : Fin (hns + 1) := strm 6 (by decide)
/-- The number `p`. -/
noncomputable def sZp : Fin (hns + 1) := strm 7 (by decide)
/-- The cut count. -/
noncomputable def sZG : Fin (hns + 1) := strm 8 (by decide)
/-- The ruler of the call site. -/
noncomputable def sL : Fin (hns + 1) := strm 9 (by decide)
/-- The tally of the call site. -/
noncomputable def sTA : Fin (hns + 1) := strm 10 (by decide)
/-- The guard of the call site. -/
noncomputable def sGA : Fin (hns + 1) := strm 11 (by decide)
/-- The (unused) target of the cut count. -/
noncomputable def sCD : Fin (hns + 1) := strm 12 (by decide)
/-- The bank of the column printer. -/
noncomputable def sbank (j : Fin tc) : Fin (hns + 1) := ⟨13 + j.val, by have := j.isLt; simp only [hns]; omega⟩

theorem sbank_inj : Function.Injective sbank := fun a b h => Fin.ext (by
  have := congrArg Fin.val h; simp [sbank] at this; omega)

theorem sne {a b : Fin (hns + 1)} (h : a.val ≠ b.val) : a ≠ b := fun e => h (congrArg Fin.val e)

/-- The registers of the call site. -/
def siteRegs : Fin 4 ↪ Fin hnr :=
  ⟨fun i => ⟨48 + i.val, by have := i.isLt; show 48 + i.val < 56; omega⟩, fun a b h => Fin.ext (by have := congrArg Fin.val h; simp at this; omega)⟩

/-- **The call site** of the column printer. -/
noncomputable def site : Site colWF.program hns hnr where
  bank := sbank
  tally := sTA
  guard := sGA
  ruler := sL
  regs := siteRegs
  bank_inj := sbank_inj
  tally_ne := fun j => sne (by simp [sbank, sTA, strm]; omega)
  guard_ne := fun j => sne (by simp [sbank, sGA, strm]; omega)
  ruler_ne := fun j => sne (by simp [sbank, sL, strm]; omega)
  tally_guard := sne (by simp [sTA, sGA, strm])
  tally_ruler := sne (by simp [sTA, sL, strm])
  guard_ruler := sne (by simp [sGA, sL, strm])

/-! ## Appending fixed bits -/

variable {ns nr : ℕ} (cap : ℕ)

/-- Append the bits of `l`. -/
def emitList (o : Fin (ns + 1)) (OP : Fin nr) : List Bool → WM ns nr
  | [] => .skip
  | b :: l => .seq (emitC o OP b) (emitList o OP l)

theorem emitList_exec (o : Fin (ns + 1)) (OP : Fin nr) :
    ∀ (l : List Bool) (σ : WState ns nr), σ.sh o = (σ.st o).length → σ.val OP + l.length ≤ cap →
      WExec cap (emitList o OP l) σ (appendO σ o OP l) (8 * l.length)
  | [], σ, _, _ => by
    rw [appendO_nil]; exact WExec.skip σ
  | b :: l, σ, ho, hc => by
    have e1 := emitC_app cap o OP b σ ho (by simp at hc; omega)
    have e2 := emitList_exec o OP l (appendO σ o OP [b]) (by simp [ho]) (by simp at hc ⊢; omega)
    rw [appendO_append] at e2
    exact WExec.mono (WExec.seq e1 e2) (by simp; omega)

/-- One bit at depth three: `marks (marks (marks [b]))`. -/
def deep3 (b : Bool) : List Bool := [true, true, true, true, true, true, true, b]

theorem deep3_eq (u : List Bool) :
    u.flatMap deep3 = Streaming.marks (Streaming.marks (Streaming.marks u)) := by
  induction u with
  | nil => simp [Streaming.marks]
  | cons b u ih =>
    simp only [List.flatMap_cons, ih]
    simp [Streaming.marks, deep3]

/-- The emitter of one bit at depth three. -/
def emitDeep (o : Fin (ns + 1)) (OP : Fin nr) (b : Bool) : WM ns nr := emitList o OP (deep3 b)

theorem emits_deep (o : Fin (ns + 1)) (OP : Fin nr) :
    NearCubicGates.Close.Recovery.HTParts.Emits cap o OP deep3 (emitDeep o OP) 64 := fun b τ ho hc => by
  unfold emitDeep
  have := emitList_exec cap o OP (deep3 b) τ ho hc
  simpa [deep3] using this

end NearQuarticWires.StageNativeHeader
