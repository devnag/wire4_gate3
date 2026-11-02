import Proof.Quartic.StageCertTests.ScheduleLoad
import Proof.Quartic.StageCertTests.ActualPlan
import Proof.Quartic.StageCertTests.FlagArithmetic

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertTests

open NearCubicGates.Close.Cells

/-- `eq:testX`–`eq:testPhi`, paper/paper.tex:
the three whole-table test families use three exact scalar powers. -/
inductive ThresholdKind where
  | population | digit | finalError
  deriving DecidableEq

/-- `eq:testX`–`eq:testPhi`, paper/paper.tex:
the population exponent is twice the trace parameter; the two
masked moment exponents are eight times that parameter. -/
def ThresholdKind.multiplier : ThresholdKind → ℕ
  | .population => 2 | .digit => 8 | .finalError => 8

/-- `eq:testX`–`eq:testPhi`, paper/paper.tex:
the base is read from its exact retained public scalar. -/
def ThresholdKind.field : ThresholdKind → ScheduleField
  | .population => .populationBase | .digit => .digitBase | .finalError => .errorBase

/-- `eq:testX`, paper/paper.tex:
only the population threshold increments its selected base. -/
def ThresholdKind.increment : ThresholdKind → ℕ
  | .population => 1 | .digit => 0 | .finalError => 0

/-- `eq:testX`–`eq:testPhi`, paper/paper.tex:
the actual scalar power associated with each strict-test family. -/
def ThresholdKind.threshold (kind : ThresholdKind) (p : Cells.Parameters) : ℕ :=
  (kind.field.value p+kind.increment)^(p.k*kind.multiplier)

/-- `prop:time`, paper/paper.tex:
every partial ordinary power fits once its complete power and the
unit value fit, including a zero base. -/
theorem power_le_final_add_one (base exponent powerIndex : ℕ) (h : powerIndex ≤ exponent) :
    base^powerIndex ≤ base^exponent+1 := by
  by_cases hb : base=0
  · subst base
    cases powerIndex <;> simp
  · exact (Nat.pow_le_pow_right (by omega : 1 ≤ base) h).trans (by omega)

/-- `eq:testX`–`eq:testPhi`, paper/paper.tex:
the ordinary power evaluator uses bounded retained scratch fields. -/
def thresholdFactor : Fin VV := ⟨79,by decide⟩
def thresholdExponent : Fin VV := ⟨80,by decide⟩
def thresholdBase : Fin VV := ⟨81,by decide⟩

/-- `eq:testX`–`eq:testPhi`, paper/paper.tex:
the actual program constructs its small multiplier, computes its
exponent and evaluates the literal selected power by ordinary arithmetic. -/
def thresholdPower (kind : ThresholdKind) : St VV MM :=
  .seq (setK thresholdFactor kind.multiplier)
    (.seq (.op (.mul ScheduleField.k.variable thresholdFactor thresholdExponent))
      (.seq (.op (.copy thresholdBase kind.field.variable))
        (.seq (incS thresholdBase kind.increment)
          (powP thresholdBase thresholdExponent thresholdVar))))

/-- `eq:testX`–`eq:testPhi` and `prop:time`, paper/paper.tex: actual retained public parameters produce
the exact strict threshold, with every power multiplication charged. -/
theorem thresholdPower_spec (C : Ctx) (a : DS VV MM) (p : Cells.Parameters)
    (kind : ThresholdKind) (hc : Cst a)
    (hfields : ∀ field : ScheduleField, a.env field.variable = field.value p)
    (hsmall : 8 < 2^C.Wd) (hexp : 8*p.k < 2^C.Wd)
    (hbase : kind.field.value p+kind.increment < 2^C.Wd)
    (hpower : kind.threshold p+1 < 2^C.Wd) :
    Hs C (thresholdPower kind) a (7*(p.k*kind.multiplier)+40) (fun b =>
      b.env thresholdVar = kind.threshold p ∧ b.sh = a.sh ∧ Cst b ∧
      Fr a b [thresholdFactor,thresholdExponent,thresholdBase,thresholdVar,a1,c4,vJ]) := by
  have hm : kind.multiplier ≤ 8 := by cases kind <;> decide
  have hi : kind.increment ≤ 1 := by cases kind <;> decide
  have hk : a.env ScheduleField.k.variable = p.k := hfields .k
  have hv : a.env kind.field.variable = kind.field.value p := hfields kind.field
  unfold thresholdPower
  refine (Hs.seq (t2 := 7*(p.k*kind.multiplier)+20)
    (setK_spec thresholdFactor (by decide) kind.multiplier a (by omega))
    fun b ⟨hbfactor,hbsh,hbfr⟩ => ?_).mono (by omega) (fun _ h => h)
  have hbk : b.env ScheduleField.k.variable = p.k := by rw [hbfr _ (by decide),hk]
  have hbb : b.env kind.field.variable = kind.field.value p := by
    rw [hbfr _ (by cases kind <;> decide),hv]
  refine (Hs.seq (t2 := 7*(p.k*kind.multiplier)+18)
    (hs_mul C ScheduleField.k.variable thresholdFactor thresholdExponent b
      (by decide) (by decide) (by decide) (by rw [hbk,hbfactor];nlinarith))
    fun d hd => ?_).mono (by omega) (fun _ h => h)
  subst d
  let d := b.set thresholdExponent (b.env ScheduleField.k.variable*b.env thresholdFactor)
  have hde : d.env thresholdExponent = p.k*kind.multiplier := by simp [d,hbk,hbfactor]
  have hdb : d.env kind.field.variable = kind.field.value p := by
    simp (config := {decide := true}) [d,DS.set,show kind.field.variable ≠ thresholdExponent by cases kind <;> decide,hbb]
  refine (Hs.seq (t2 := 7*(p.k*kind.multiplier)+16)
    (hs_copy C thresholdBase kind.field.variable d (by cases kind <;> decide))
    fun e he => ?_).mono (by omega) (fun _ h => h)
  subst e
  let e := d.set thresholdBase (d.env kind.field.variable)
  have heb : e.env thresholdBase = kind.field.value p := by simp [e,hdb]
  refine (Hs.seq (t2 := 7*(p.k*kind.multiplier)+8)
    (incS_spec thresholdBase (by decide) kind.increment e (by rw [heb];exact hbase))
    fun f ⟨hfb,hfsh,hffr⟩ => ?_).mono (by omega) (fun _ h => h)
  have hfbase : f.env thresholdBase = kind.field.value p+kind.increment := by simpa [heb] using hfb
  have hfexp : f.env thresholdExponent = p.k*kind.multiplier := by
    rw [hffr _ (by decide)]
    simpa (config := {decide := true}) [e,DS.set] using hde
  have hfr : Fr a f [thresholdFactor,thresholdExponent,thresholdBase,vJ] :=
    Fr.trans (Fr.weaken hbfr (by decide))
      (Fr.trans (Fr.set _ _ (by decide))
        (Fr.trans (Fr.set _ _ (by decide)) (Fr.weaken hffr (by decide))))
  have hfc : Cst f := Cst.of_fr hc hfr (by decide)
  have hpowfit : ∀ t ≤ f.env thresholdExponent, f.env thresholdBase^t < 2^C.Wd := by
    intro t ht
    rw [hfbase]
    have hh := power_le_final_add_one (kind.field.value p+kind.increment) (p.k*kind.multiplier) t
      (by simpa [hfexp] using ht)
    exact hh.trans_lt hpower
  have hpe := powP_spec (C := C) thresholdBase thresholdExponent thresholdVar (by decide)
    f hpowfit (by rw [hfexp];nlinarith) (by omega)
  rw [hfexp] at hpe
  refine hpe.mono (by omega) ?_
  rintro g ⟨hgv,hgsh,hgfr⟩
  have htotal : Fr a g [thresholdFactor,thresholdExponent,thresholdBase,thresholdVar,a1,c4,vJ] :=
    Fr.trans (Fr.weaken hfr (by decide)) (Fr.weaken hgfr (by decide))
  refine ⟨by simpa only [hfbase,hfexp,ThresholdKind.threshold] using hgv,
    hgsh.trans (hfsh.trans hbsh),Cst.of_fr hc htotal (by decide),htotal⟩

end NearQuarticWires.StageCertTests
