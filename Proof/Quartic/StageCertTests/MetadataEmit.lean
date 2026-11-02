import Proof.Quartic.StageCertTests.TestMetadata
import Proof.Quartic.StageCertTests.ThresholdPower
import Proof.Quartic.StageRecovery.NaturalPrint

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertTests

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells
open StageRecovery (emitVariable emitVariable_spec)

/-- `sec:algorithm`, paper/paper.tex:
natural metadata fields are emitted in sequence by the actual
self-delimiting integer-field printer. -/
def emitMetadataFields : List (Fin VV) → St VV MM
  | [] => skipS
  | x :: xs => .seq (emitVariable x) (emitMetadataFields xs)

/-- `sec:algorithm` and `prop:time`, paper/paper.tex: literal scalar-field output charges its complete
binary codec and preserves all retained test indices and parameters. -/
theorem emitMetadataFields_spec (xs : List (Fin VV)) (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (hsafe : ∀ x ∈ xs, x ∉ [t3,t5,t6,t7,t8,t9]) (hW : 2 ≤ C.Wd)
    (hfit : ∀ x ∈ xs, natBitLength (a.env x)+2 < 2^C.Wd) :
    Hs C (emitMetadataFields xs) a
      ((xs.map fun x => 40*natBitLength (a.env x)+43).sum+1) (fun b =>
        b.out = a.out ++ (xs.map a.env).flatMap natWord ∧
        (b.ip,b.ram,b.rc,b.kin,b.kout,b.kc) = (a.ip,a.ram,a.rc,a.kin,a.kout,a.kc) ∧
        Cst b ∧ Fr a b [t3,t5,t6,t7,t8,t9,vJ]) := by
  induction xs generalizing a with
  | nil =>
      refine (skip_spec (C := C) a).mono (by simp) ?_
      rintro b rfl
      exact ⟨by simp,rfl,Cst.of_fr (T := [vJ]) hc (Fr.set _ _ (by decide)) (by decide),Fr.set _ _ (by decide)⟩
  | cons x xs ih =>
      unfold emitMetadataFields
      have hx : x ≠ t3 := by
        intro he
        apply hsafe x (by simp)
        rw [he]
        decide
      refine (Hs.seq (t2 := (xs.map fun y => 40*natBitLength (a.env y)+43).sum+1)
        (emitVariable_spec C a hc x hx hW (hfit x (by simp)))
        fun b ⟨hbo,hbr,hbc,hbf⟩ => ?_).mono (by simp;omega) (fun _ h => h)
      have heq : xs.map b.env = xs.map a.env := by
        apply List.map_congr_left
        intro y hy
        exact hbf y (hsafe y (by simp [hy]))
      have hfitb : ∀ y ∈ xs, natBitLength (b.env y)+2 < 2^C.Wd := by
        intro y hy
        rw [hbf y (hsafe y (by simp [hy]))]
        exact hfit y (by simp [hy])
      have hbsteps : (xs.map fun y => 40*natBitLength (b.env y)+43).sum =
          (xs.map fun y => 40*natBitLength (a.env y)+43).sum := by
        apply congrArg List.sum
        apply List.map_congr_left
        intro y hy
        rw [hbf y (hsafe y (by simp [hy]))]
      have hr := ih b hbc (fun y hy => hsafe y (by simp [hy])) hfitb
      rw [hbsteps] at hr
      refine hr.mono le_rfl ?_
      rintro d ⟨hdo,hdr,hdc,hdf⟩
      refine ⟨?_,hdr.trans hbr,hdc,Fr.trans (Fr.weaken hbf (by decide)) hdf⟩
      rw [hdo,heq,hbo]
      simp [List.append_assoc]

/-- `sec:algorithm`, paper/paper.tex:
the kind, circuit and digit ordinal have dedicated retained registers. -/
def testTagVar : Fin VV := ⟨82,by decide⟩
def testCircuitVar : Fin VV := ⟨83,by decide⟩
def testDigitVar : Fin VV := ⟨84,by decide⟩

/-- `sec:algorithm`, paper/paper.tex:
the exact five-field record follows the agreed natural metadata codec. -/
def metadataVariables : List (Fin VV) :=
  [testTagVar,testCircuitVar,signOrdinal,testDigitVar,thresholdVar]

/-- `sec:algorithm`, paper/paper.tex:
the physical metadata printer emits precisely the five public
fields, retaining every source word and arithmetic parameter. -/
theorem emitTestMetadata_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (metadata : TestMetadata)
    (ht : a.env testTagVar = metadata.tag) (hj : a.env testCircuitVar = metadata.circuit)
    (hs : a.env signOrdinal = metadata.signOrdinal) (hr : a.env testDigitVar = metadata.digitOrdinal)
    (hb : a.env thresholdVar = metadata.threshold) (hW : 2 ≤ C.Wd)
    (hfit : ∀ x ∈ metadataVariables, natBitLength (a.env x)+2 < 2^C.Wd) :
    Hs C (emitMetadataFields metadataVariables) a
      (40*(natBitLength metadata.tag+natBitLength metadata.circuit+
        natBitLength metadata.signOrdinal+natBitLength metadata.digitOrdinal+
        natBitLength metadata.threshold)+216) (fun b =>
        b.out = a.out ++ metadata.word ∧
        (b.ip,b.ram,b.rc,b.kin,b.kout,b.kc) = (a.ip,a.ram,a.rc,a.kin,a.kout,a.kc) ∧
        Cst b ∧ Fr a b [t3,t5,t6,t7,t8,t9,vJ]) := by
  refine (emitMetadataFields_spec metadataVariables C a hc (by decide) hW hfit).mono ?_ ?_
  · simp only [metadataVariables,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,ht,hj,hs,hr,hb]
    omega
  · rintro b ⟨hbo,hbr,hbc,hbf⟩
    refine ⟨?_,hbr,hbc,hbf⟩
    rw [hbo]
    simp [metadataVariables,ht,hj,hs,hr,hb,TestMetadata.word,List.append_assoc]

end NearQuarticWires.StageCertTests
