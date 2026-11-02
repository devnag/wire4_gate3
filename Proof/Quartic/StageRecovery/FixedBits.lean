import Proof.Quartic.StageLift.Literal
import Proof.Quartic.StageRecovery.CacheEval
import Proof.Wire_3_5.GF2Machines

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery.FixedBits

open NearCubicGates.Close.Cells

/-- `lem:print`, paper/paper.tex: the binary value
being physically written into a finite family setup field. -/
def value : Fin VV := ⟨120, by decide⟩
/-- `lem:print`, paper/paper.tex: the finite family
field width, retained throughout its complete bit serialization. -/
def width : Fin VV := ⟨121, by decide⟩
/-- `lem:print`, paper/paper.tex: the physical bit
position within one fixed-width family setup field. -/
def index : Fin VV := ⟨122, by decide⟩
/-- `lem:print`, paper/paper.tex: the next shifted
word in low-to-high family field serialization. -/
def quotient : Fin VV := ⟨123, by decide⟩
/-- `lem:print`, paper/paper.tex: one binary digit
obtained by division by two during family field serialization. -/
def digit : Fin VV := ⟨124, by decide⟩

/-- `lem:print`, paper/paper.tex: output emission
retains every source, store and callee component. -/
def outputRest (a : DS VV MM) := (a.ip, a.ram, a.rc, a.kin, a.kout, a.kc)

/-- `lem:print`, paper/paper.tex: two nested framing
layers contribute three true markers before each actual binary digit. -/
def bitGroup (b : Bool) : List Bool := [true, true, true, b]

/-- `lem:print`, paper/paper.tex: one binary digit is
emitted by four literal ordinary output operations and a Boolean test. -/
def emitBitGroup : St VV MM :=
  .seq (StageLift.emitLiteral [true, true, true]) (emitB .emit digit)

/-- `lem:print`, paper/paper.tex: the physical digit
emitter writes precisely its two framing layers and retains all data. -/
theorem emitBitGroup_spec (C : Ctx) (a : DS VV MM) (hc : Cst a) :
    Hs C emitBitGroup a 10 (fun b =>
      b.out = a.out ++ bitGroup (decide (a.env digit = 1)) ∧
      outputRest b = outputRest a ∧ Cst b ∧ Fr a b [vJ]) := by
  unfold emitBitGroup
  refine (Hs.seq (t2 := 2) (StageLift.emitLiteral_spec C [true, true, true] a hc)
    fun b ⟨hbo, hbr, hbc, hbf⟩ => ?_).mono (by norm_num) (fun _ h => h)
  refine (emitB_spec (snkO C) digit (by decide) b hbc trivial).mono le_rfl ?_
  rintro d ⟨hdo, hdr, hde⟩
  refine ⟨?_, hdr.trans hbr, ?_, ?_⟩
  · have hbd : b.env digit = a.env digit := hbf _ (by decide)
    simpa [snkO, hbo, hbd, bitGroup, List.append_assoc] using hdo
  · exact ⟨by rw [hde]; exact hbc.z, by rw [hde]; exact hbc.one, by rw [hde]; exact hbc.two⟩
  · intro y hy
    rw [hde]
    exact hbf y hy

/-- `lem:print`, paper/paper.tex: the exact finite
register frame of one actual binary output step. -/
def bitScratch : List (Fin VV) := [value, quotient, digit, vJ]

/-- `lem:print`, paper/paper.tex: one actual bit step
divides the word by two, emits the remainder, and keeps the quotient. -/
def bitStep : St VV MM :=
  .seq (.op (.dm value v2 quotient digit))
    (.seq emitBitGroup (.op (.copy value quotient)))

/-- `lem:print`, paper/paper.tex: an ordinary binary
step emits its genuine low digit and retains every other physical state
component; its bounded clock is independent of the value's magnitude. -/
theorem bitStep_spec (C : Ctx) (a : DS VV MM) (hc : Cst a) (v : ℕ)
    (hv : a.env value = v) (hW : 2 ≤ C.Wd) :
    Hs C bitStep a 14 (fun b =>
      b.env value = v / 2 ∧ b.out = a.out ++ bitGroup (decide (v % 2 = 1)) ∧
      outputRest b = outputRest a ∧ Cst b ∧ Fr a b bitScratch) := by
  have hfour : 4 ≤ 2 ^ C.Wd :=
    (show 4 = 2 ^ 2 by norm_num).le.trans (Nat.pow_le_pow_right (by decide) hW)
  unfold bitStep
  refine Hs.seq (t2 := 12) (hs_dm C value v2 quotient digit a
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [hc.two]; omega) (by rw [hc.two]; omega)) fun b hb => ?_
  subst b
  let d := (a.set quotient (v / 2)).set digit (v % 2)
  have hd : (a.set quotient (a.env value / a.env v2)).set digit (a.env value % a.env v2) = d := by
    rw [hv, hc.two]
  rw [hd]
  have hdf : Fr a d bitScratch := Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide))
  have hdc : Cst d := Cst.of_fr hc hdf (by decide)
  refine Hs.seq (t2 := 1) (emitBitGroup_spec C d hdc) fun e ⟨heo, her, hec, hef⟩ => ?_
  refine (hs_copy C value quotient e (by decide)).mono le_rfl ?_
  rintro f rfl
  refine ⟨?_, ?_, her, Cst.of_fr (T := [value]) hec (Fr.set _ _ (by decide)) (by decide), ?_⟩
  · rw [DS.set_env_self, hef _ (by decide)]
    simp (config := {decide := true}) [d, DS.set]
  · simpa (config := {decide := true}) [d, DS.set] using heo
  · exact Fr.trans hdf (Fr.trans (Fr.weaken hef (by decide)) (Fr.set _ _ (by decide)))

end NearQuarticWires.StageRecovery.FixedBits
