import Proof.Quartic.StageLift.UnaryMarkers
import Proof.Quartic.StageLift.StreamArithmetic

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicGates.Close.Cells
open NearQuarticWires.StageRecovery

/-- `lem:print`, paper/paper.tex: payload replay
changes only bit flags and the reduced accumulator/place-value workspace. -/
def payloadBodyScratch : List (Fin VV) :=
  [t0, t1, leftVar, rightVar, streamPowerVar, quotientVar, remainderVar, vJ]

/-- `lem:print`, paper/paper.tex: one payload bit
is read, its bounded modular contribution accumulated, its reduced place
value doubled, and the next actual marker/sentinel record inspected. -/
def streamPayloadBody (store : Fin MM) : St VV MM :=
  .seq (.op (.rdI t1)) (.seq addStreamBit
    (.seq doubleStreamPower (.op (.rdM store t0))))

/-- `lem:print`, paper/paper.tex: a complete
streamed payload step uses only modulus-bounded arithmetic and an
explicit in-range marker read, including when that marker is zero. -/
theorem streamPayloadBody_spec (C : Ctx) (store : Fin MM) (a : DS VV MM) (hc : Cst a)
    (q value power : ℕ) (bit next : Bool) (rest : List Bool) (hq : 0 < q)
    (haq : a.env modulusVar = q) (hav : a.env leftVar = value)
    (hap : a.env streamPowerVar = power) (hv : value < q) (hp : power < q)
    (hfit : 2 * q ≤ 2 ^ C.Wd)
    (hin : C.inp.drop a.ip = bit :: rest)
    (hmark : a.rc store < (a.ram store).length)
    (hnext : (a.ram store).getD (a.rc store) 0 = next.toNat) :
    Hs C (streamPayloadBody store) a 18 (fun b =>
      b.env leftVar = (value + if bit then power else 0) % q ∧
      b.env streamPowerVar = (2 * power) % q ∧ b.env t0 = next.toNat ∧
      b.ip = a.ip + 1 ∧ b.ram = a.ram ∧
      b.rc = Function.update a.rc store (a.rc store + 1) ∧
      (b.out, b.kin, b.kout, b.kc) = (a.out, a.kin, a.kout, a.kc) ∧
      Cst b ∧ Fr a b payloadBodyScratch) := by
  unfold streamPayloadBody
  refine Hs.seq (t1 := 1) (t2 := 16)
    (readInputBit_spec C t1 a bit rest hin) fun b hb => ?_
  subst b
  let a' : DS VV MM := { a.set t1 bit.toNat with ip := a.ip + 1 }
  have h₁ : Fr a a' payloadBodyScratch := Fr.set a _ (by simp [payloadBodyScratch])
  have hc' := Cst.of_fr hc h₁ (by decide)
  have haq' : a'.env modulusVar = q := by simpa (config := {decide := true}) [a', DS.set] using haq
  have hav' : a'.env leftVar = value := by simpa (config := {decide := true}) [a', DS.set] using hav
  have hap' : a'.env streamPowerVar = power := by simpa (config := {decide := true}) [a', DS.set] using hap
  refine Hs.seq (t1 := 8) (t2 := 7)
    (addStreamBit_spec C a' hc' q value power bit hq haq' hav' hap'
      (by simp [a']) hv hp hfit) fun b ⟨hbl, hbsh, hbc, hbf⟩ => ?_
  have hbq : b.env modulusVar = q := by rw [hbf _ (by decide)]; exact haq'
  have hbp : b.env streamPowerVar = power := by rw [hbf _ (by decide)]; exact hap'
  refine Hs.seq (t1 := 5) (t2 := 1)
    (doubleStreamPower_spec C b hbc q power hq hbq hbp hp hfit)
    fun d ⟨hdp, hdsh, hdc, hdf⟩ => ?_
  have hs : Same a' d := (Same.of_sh hbsh).trans (Same.of_sh hdsh)
  have hdram : d.ram = a.ram := hs.ram
  have hdrc : d.rc = a.rc := hs.rc
  refine (hs_rdM C store t0 d (by rw [hdram, hdrc]; exact hmark)).mono le_rfl ?_
  rintro e rfl
  have hlast : Fr d ((d.set t0 ((d.ram store).getD (d.rc store) 0)).adv store)
      payloadBodyScratch := Fr.set d _ (by simp [payloadBodyScratch])
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, Cst.of_fr hdc hlast (by decide), ?_⟩
  · change (d.set t0 ((d.ram store).getD (d.rc store) 0)).env leftVar = _
    rw [DS.set_env_ne _ _ (by decide), hdf _ (by decide)]
    exact hbl
  · change (d.set t0 ((d.ram store).getD (d.rc store) 0)).env streamPowerVar = _
    rw [DS.set_env_ne _ _ (by decide)]
    exact hdp
  · simp only [DS.adv, DS.set_env_self, hdram, hdrc, hnext]
  · exact hs.ip
  · exact hdram
  · simp only [DS.adv, DS.set, hdrc]
  · change (d.out, d.kin, d.kout, d.kc) = (a.out, a.kin, a.kout, a.kc)
    rw [hs.out, hs.kin, hs.kout, hs.kc]
    rfl
  · exact h₁.trans ((hbf.weaken (by simp [payloadBodyScratch])).trans
      ((hdf.weaken (by simp [payloadBodyScratch])).trans hlast))

end NearQuarticWires.StageLift
