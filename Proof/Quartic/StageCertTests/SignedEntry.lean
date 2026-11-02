import Proof.Quartic.StageRecovery.PacketFields
import Proof.Gates.WordPrograms.SInt

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertTests

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open NearCubicGates.Close.WordPrograms.SInt (encS encS_div encS_mod)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open StageRecovery (signVar magnitudeVar emitVariable emitVariable_spec)

/-- `lem:print`, paper/paper.tex:
the ordinary signed codec stores the sign and magnitude of a native entry. -/
theorem signed_parts_intWord (z : ℤ) :
    intWord z = natWord (if z < 0 then 1 else 0) ++ natWord z.natAbs := rfl

/-- `lem:print`, paper/paper.tex:
the exact signed output consists of two physically emitted natural fields. -/
def emitSignedFields : St VV MM := .seq (emitVariable signVar) (emitVariable magnitudeVar)

/-- `lem:print`, paper/paper.tex:
emitting native signed fields retains the sign on arbitrary columns. -/
theorem emitSignedFields_spec (C : Ctx) (a : DS VV MM) (hc : Cst a) (z : ℤ)
    (hs : a.env signVar = if z < 0 then 1 else 0)
    (hm : a.env magnitudeVar = z.natAbs) (hW : 2 ≤ C.Wd)
    (hsfit : natBitLength (if z < 0 then 1 else 0) + 2 < 2 ^ C.Wd)
    (hmfit : natBitLength z.natAbs + 2 < 2 ^ C.Wd) :
    Hs C emitSignedFields a
      (40 * natBitLength (if z < 0 then 1 else 0) + 40 * natBitLength z.natAbs + 85)
      (fun b => b.out = a.out ++ intWord z ∧
        (b.ip, b.ram, b.rc, b.kin, b.kout, b.kc) =
          (a.ip, a.ram, a.rc, a.kin, a.kout, a.kc) ∧
        Cst b ∧ Fr a b [t3,t5,t6,t7,t8,t9]) := by
  unfold emitSignedFields
  have e1 := emitVariable_spec C a hc signVar (by decide) hW
    (by rw [hs]; exact hsfit)
  rw [hs] at e1
  refine (Hs.seq (t2 := 40 * natBitLength z.natAbs + 42) e1
    fun b ⟨ho,hr,hbc,hbf⟩ => ?_).mono (by omega) (fun _ h => h)
  have hbm : b.env magnitudeVar = z.natAbs := by rw [hbf _ (by decide),hm]
  have e2 := emitVariable_spec C b hbc magnitudeVar (by decide) hW
    (by rw [hbm]; exact hmfit)
  rw [hbm] at e2
  refine e2.mono le_rfl ?_
  rintro d ⟨hdo,hdr,hdc,hdf⟩
  refine ⟨?_,hdr.trans hr,hdc,Fr.trans hbf hdf⟩
  rw [hdo,ho,signed_parts_intWord,List.append_assoc]

/-- `lem:print`, paper/paper.tex:
one literal native signed record is decoded and emitted in the canonical codec. -/
def signedEntry : St VV MM :=
  .seq rdRec (.seq (.op (.dm t3 v2 magnitudeVar signVar)) emitSignedFields)

/-- `prop:time`, paper/paper.tex:
every native byte read and canonical sign or magnitude write is charged. -/
def signedEntryCost (width : ℕ) (z : ℤ) : ℕ :=
  12 * width + 12 + (1 +
    (40 * natBitLength (if z < 0 then 1 else 0) + 40 * natBitLength z.natAbs + 85) + 1) + 1

/-- `lem:print`, paper/paper.tex:
the physical converter preserves signed values, source position and
all registers outside its explicit bounded scratch set. -/
theorem signedEntry_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (width : ℕ) (z : ℤ) (rest : List Bool)
    (hin : C.inp.drop a.ip = frame (binary width (encS z)) ++ rest)
    (hz : encS z < 2 ^ width) (hwidth : width + 2 ≤ C.Wd)
    (hfour : 4 ≤ 2 ^ C.Wd)
    (hsfit : natBitLength (if z < 0 then 1 else 0) + 2 < 2 ^ C.Wd)
    (hmfit : natBitLength z.natAbs + 2 < 2 ^ C.Wd) :
    Hs C signedEntry a (signedEntryCost width z) (fun b =>
      b.out = a.out ++ intWord z ∧ b.ip = a.ip + (2 * width + 1) ∧ Cst b ∧
      Fr a b [t0,t1,t3,vJ,magnitudeVar,signVar,t5,t6,t7,t8,t9]) := by
  unfold signedEntry signedEntryCost
  refine Hs.seq (rdRec_spec a hc width (encS z) rest hin hz hwidth)
    fun b ⟨hbv,hbp,hbr,hbf⟩ => ?_
  have hbc : Cst b := Cst.of_fr hc hbf (by decide)
  refine Hs.seq (hs_dm C t3 v2 magnitudeVar signVar b
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [hbc.two]; norm_num) (by rw [hbc.two]; exact hfour)) fun d hd => ?_
  subst d
  let s := (b.set magnitudeVar (b.env t3 / b.env v2)).set signVar (b.env t3 % b.env v2)
  have hsm : s.env magnitudeVar = z.natAbs := by
    simp (config := {decide := true}) [s,DS.set,hbv,hbc.two,encS_div]
  have hss : s.env signVar = if z < 0 then 1 else 0 := by
    simp [s,hbv,hbc.two,encS_mod]
  have hsc : Cst s := Cst.of_fr (T := [magnitudeVar,signVar]) hbc
    (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide))) (by decide)
  refine (emitSignedFields_spec C s hsc z hss hsm (by omega) hsfit hmfit).mono le_rfl ?_
  rintro e ⟨heo,her,hec,hef⟩
  have hbi : e.ip = b.ip := congrArg Prod.fst her
  have hbo : b.out = a.out := congrArg Prod.fst hbr
  refine ⟨by simpa only [s,DS.set] using heo.trans (congrArg (· ++ intWord z) hbo),
    by rw [hbi,hbp],hec,?_⟩
  exact Fr.trans (Fr.weaken hbf (by decide))
    (Fr.trans (Fr.set _ _ (by decide))
      (Fr.trans (Fr.set _ _ (by decide)) (Fr.weaken hef (by decide))))

end NearQuarticWires.StageCertTests
