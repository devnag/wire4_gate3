import Proof.Gates.WordPrograms.BinWDiv
import Proof.Gates.WordPrograms.SInt
import Proof.Quartic.StageRecovery.ModReduce

set_option autoImplicit false

namespace NearQuarticWires.StageModularCuts

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicGates.Close.WordPrograms

abbrev State := WState 15 16
abbrev Program := WMX 15 16

def coefficient : Fin 16 := 6
def modulus : Fin 16 := 7
def magnitude : Fin 16 := 8
def quotient : Fin 16 := 9
def remainder : Fin 16 := 10
def temporary : Fin 16 := 11

def sign : Fin 16 := 0
def flag : Fin 16 := 1
def rewind : Fin 16 := 2
def rounds : Fin 16 := 3
def counter : Fin 16 := 4

/-- `lem:print`, paper/paper.tex: the fixed binary
work words for signed coefficient reduction occupy distinct tapes. -/
structure Words (a : State) (W x q u v t : ℕ) : Prop where
  input : NumOn a magnitude W x
  divisor : NumOn a modulus W q
  quotient : NumOn a quotient W u
  remainder : NumOn a remainder W v
  temporary : NumOn a temporary W t

/-- `lem:print`, paper/paper.tex: the four arithmetic
counters are clear between fixed-width operations. -/
structure Clear (a : State) : Prop where
  flag : a.val flag = 0
  rewind : a.val rewind = 0
  rounds : a.val rounds = 0
  counter : a.val counter = 0

def divided (a : State) (W x q : ℕ) : State :=
  ((a.sets quotient (frame (binary W (x / q)))).sets remainder
    (frame (binary W (x % q)))).sets temporary (frame (binary W 0))

def divide : Program :=
  BinW.divmod magnitude modulus quotient remainder temporary flag rewind rounds counter

/-- `lem:print`, paper/paper.tex: binary long division
reads a bounded binary divisor and leaves all arithmetic counters clear. -/
theorem divide_spec (cap W : ℕ) (a : State) (x q u v t : ℕ)
    (hw : Words a W x q u v t) (hc : Clear a)
    (hx : x < 2 ^ W) (hq : 0 < q) (hfit : 2 * q ≤ 2 ^ W)
    (hcap : 2 * W + 1 ≤ cap) :
    WXExec cap divide a (divided a W x q) (BinW.divCost W) := by
  exact BinW.divmod_spec cap W (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    a x q u v t hw.input hw.divisor hw.quotient hw.remainder hw.temporary
    hc.flag hc.rewind hc.rounds hc.counter hx hq hfit hcap

/-- `lem:print`, paper/paper.tex: division changes only
its quotient, remainder, and temporary binary words. -/
theorem divided_words (a : State) (W x q u v t : ℕ)
    (hw : Words a W x q u v t) :
    Words (divided a W x q) W x q (x / q) (x % q) 0 := by
  constructor
  · exact BinW.numOn_sets_ne (BinW.numOn_sets_ne
      (BinW.numOn_sets_ne hw.input (by decide) _) (by decide) _) (by decide) _
  · exact BinW.numOn_sets_ne (BinW.numOn_sets_ne
      (BinW.numOn_sets_ne hw.divisor (by decide) _) (by decide) _) (by decide) _
  · exact BinW.numOn_sets_ne (BinW.numOn_sets_ne
      (BinW.numOn_sets_self a quotient W (x / q) hw.quotient.2)
      (by decide) _) (by decide) _
  · exact BinW.numOn_sets_ne
      (BinW.numOn_sets_self _ remainder W (x % q) hw.remainder.2) (by decide) _
  · exact BinW.numOn_sets_self _ temporary W 0 hw.temporary.2

/-- `lem:print`, paper/paper.tex: binary division
preserves every scalar register. -/
theorem divided_clear (a : State) (W x q : ℕ) (hc : Clear a) :
    Clear (divided a W x q) :=
  ⟨hc.flag, hc.rewind, hc.rounds, hc.counter⟩

/-- `lem:print`, paper/paper.tex: signed normalization
uses a nonnegative canonical residue for every positive modulus. -/
theorem signed_residue_lt (q v : ℕ) (s : Bool) (hq : 0 < q) :
    StageRecovery.signedNaturalResidue q v s < q := by
  cases s <;> exact Nat.mod_lt _ hq

end NearQuarticWires.StageModularCuts
