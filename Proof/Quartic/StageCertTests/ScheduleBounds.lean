import Proof.Quartic.StageCertTests.ThresholdPower
import Proof.Gates.WorkerArith.GuessWordLengths

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertTests

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells

/-- `sec:params` and `eq:testX`–`eq:testPhi`, paper/paper.tex: the small scheduling header covers
the actual parameter parser, loop bounds and three unpowered bases. -/
def scheduleHeaderScalars (p : Cells.Parameters) : List ℕ :=
  StageLift.parameterHeadFields p ++ p.primes.sort (· ≤ ·) ++ StageLift.parameterTailFields p ++
    p.factors ++ [8*p.k,p.J,p.Xmax+1,p.hE,p.Lambda]

/-- `prop:time`, paper/paper.tex:
the scheduling width is controlled by binary scalar sizes rather
than by any whole-table or walk census. -/
def scheduleHint (p : Cells.Parameters) : ℕ :=
  let mass := ((scheduleHeaderScalars p).map natBitLength).sum
  10+mass+8*p.k*(mass+1)

/-- `prop:time`, paper/paper.tex:
each actual scalar's binary length is included in the header sum. -/
theorem bitLength_le_sum (values : List ℕ) (value : ℕ) (hv : value ∈ values) :
    natBitLength value ≤ (values.map natBitLength).sum := by
  induction values with
  | nil => simp at hv
  | cons x xs ih =>
      simp only [List.mem_cons] at hv
      simp only [List.map_cons,List.sum_cons]
      rcases hv with rfl | hv
      · omega
      · have := ih hv;omega

/-- `prop:time`, paper/paper.tex:
the concrete header controls each literal scalar field. -/
theorem scheduleHint_scalar (p : Cells.Parameters) (value : ℕ)
    (hv : value ∈ scheduleHeaderScalars p) : natBitLength value ≤ scheduleHint p := by
  have h := bitLength_le_sum (scheduleHeaderScalars p) value hv
  dsimp only [scheduleHint]
  omega

/-- `prop:time`, paper/paper.tex:
ordinary power width is bounded from its unpowered base and
exponent, so a cold workspace hint requires no threshold value. -/
theorem power_bitLength_le (base exponent : ℕ) :
    natBitLength (base^exponent) ≤ exponent*natBitLength base+1 := by
  have hp : base^exponent ≤ 2^(exponent*natBitLength base) := by
    calc
      base^exponent ≤ (2^natBitLength base)^exponent := Nat.pow_le_pow_left (lt_natBitLength base).le exponent
      _ = 2^(exponent*natBitLength base) := by rw [←Nat.pow_mul,Nat.mul_comm]
  exact NearCubicGates.Close.WorkerArith.WorkerBounds.nbl_le_of_lt (by omega)
    (hp.trans_lt (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _)))

/-- `sec:algorithm` and `prop:time`, paper/paper.tex: these bounds concern actual parser fields
and arithmetic powers of the selected parameters. -/
structure ScheduleBounds (C : Ctx) (p : Cells.Parameters) (B : ℕ) : Prop where
  small : 256 < 2^C.Wd
  exponent : 8*p.k < 2^C.Wd
  large : 10 ≤ B
  width : 2 ≤ C.Wd
  bitFit : B+2 < 2^C.Wd
  chainBits : natBitLength p.J ≤ B
  chainFit : p.J < 2^C.Wd
  baseFit : ∀ kind : ThresholdKind, kind.field.value p+kind.increment < 2^C.Wd
  powerFit : ∀ kind : ThresholdKind, kind.threshold p+1 < 2^C.Wd
  powerBits : ∀ kind : ThresholdKind, natBitLength (kind.threshold p) ≤ B
  parserBits : ∀ value ∈ StageLift.parameterHeadFields p ++ p.primes.sort (· ≤ ·) ++
    StageLift.parameterTailFields p ++ p.factors, natBitLength value ≤ B
  parserCounts : p.primes.card < 2^C.Wd ∧ p.factors.length < 2^C.Wd

/-- `sec:params` and `prop:time`, paper/paper.tex: an actual small-header initialization discharges
every scheduler arithmetic and parameter-parser width condition. -/
theorem scheduleBounds_of_width (C : Ctx) (p : Cells.Parameters)
    (hW : 64*(scheduleHint p+1) ≤ C.Wd) : ScheduleBounds C p (scheduleHint p) := by
  let B := scheduleHint p
  let mass := ((scheduleHeaderScalars p).map natBitLength).sum
  have hBdef : B = 10+mass+8*p.k*(mass+1) := rfl
  have hB : 10 ≤ B := by dsimp [B,scheduleHint];omega
  have hBW : B < C.Wd := by omega
  have hscalar (value : ℕ) (hv : value ∈ scheduleHeaderScalars p) : natBitLength value ≤ B :=
    scheduleHint_scalar p value hv
  have hfit (value : ℕ) (hv : value ∈ scheduleHeaderScalars p) : value < 2^C.Wd :=
    (lt_natBitLength value).trans_le (Nat.pow_le_pow_right (by decide) ((hscalar value hv).trans hBW.le))
  have hpbits (kind : ThresholdKind) : natBitLength (kind.threshold p) ≤ B := by
    have hb : natBitLength (kind.field.value p+kind.increment) ≤ mass := by
      apply bitLength_le_sum
      cases kind <;> simp [ThresholdKind.field,ThresholdKind.increment,ScheduleField.value,scheduleHeaderScalars]
    have hm : kind.multiplier ≤ 8 := by cases kind <;> decide
    have he : p.k*kind.multiplier ≤ 8*p.k := by nlinarith
    have hprod := Nat.mul_le_mul he hb
    have hp := power_bitLength_le (kind.field.value p+kind.increment) (p.k*kind.multiplier)
    change natBitLength ((kind.field.value p+kind.increment)^(p.k*kind.multiplier)) ≤ B
    rw [hBdef]
    nlinarith
  have hpfit (kind : ThresholdKind) : kind.threshold p+1 < 2^C.Wd := by
    have h := (lt_natBitLength (kind.threshold p)).trans_le
      (Nat.pow_le_pow_right (by decide) (hpbits kind))
    have hpow : 2^B < 2^C.Wd := Nat.pow_lt_pow_right (by decide) hBW
    omega
  have hparse (value : ℕ) (hv : value ∈ StageLift.parameterHeadFields p ++ p.primes.sort (· ≤ ·) ++
      StageLift.parameterTailFields p ++ p.factors) : natBitLength value ≤ B := by
    apply hscalar
    exact List.mem_append_left _ hv
  refine ⟨?_,hfit _ (by simp [scheduleHeaderScalars]),hB,by omega,?_,
    hscalar _ (by simp [scheduleHeaderScalars]),hfit _ (by simp [scheduleHeaderScalars]),?_,hpfit,hpbits,hparse,?_⟩
  · have h9 : 9 ≤ C.Wd := by omega
    have h := Nat.pow_le_pow_right (n := 2) (by decide) h9
    norm_num at h
    omega
  · have h := Nat.lt_two_pow_self (n := C.Wd)
    omega
  · intro kind
    apply hfit
    cases kind <;> simp [ThresholdKind.field,ThresholdKind.increment,ScheduleField.value,scheduleHeaderScalars]
  · constructor
    · apply hfit
      simp [scheduleHeaderScalars,StageLift.parameterHeadFields]
    · apply hfit
      simp [scheduleHeaderScalars,StageLift.parameterTailFields]

end NearQuarticWires.StageCertTests
