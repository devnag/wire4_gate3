import Proof.Quartic.StageRecovery.PacketList

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells

/-- `lem:print`, paper/paper.tex: read one actual
natural field into a retained binary variable. -/
def readVariable (x : Fin VV) : St VV MM := .seq rdNatI (.op (.copy x t3))

/-- `lem:print`, paper/paper.tex: the field parser
charges the complete encoded source field and preserves the other
literal input and output streams. -/
theorem readVariable_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (x : Fin VV) (hx : x ∉ rdNatT)
    (hxc : x ≠ vZ ∧ x ≠ v1 ∧ x ≠ v2)
    (value : ℕ) (rest : List Bool)
    (hin : C.inp.drop a.ip = natWord value ++ rest)
    (hwidth : natBitLength value + 2 ≤ C.Wd) :
    Hs C (readVariable x) a (30 * natBitLength value + 32) (fun b =>
      b.env x = value ∧ b.ip = a.ip + (natWord value).length ∧
      (b.out, b.ram, b.rc, b.kin, b.kout, b.kc) =
        (a.out, a.ram, a.rc, a.kin, a.kout, a.kc) ∧
      Cst b ∧ Fr a b (x :: rdNatT)) := by
  have hxt3 : x ≠ t3 := fun he => hx (he ▸ by decide)
  unfold readVariable
  refine (Hs.seq (t2 := 1) (rdNatI_spec a hc value rest hin hwidth)
    fun b ⟨hbv, _, hbi, hbr, hbf⟩ => ?_).mono (by omega) (fun _ h => h)
  refine (hs_copy C x t3 b hxt3).mono le_rfl ?_
  rintro d rfl
  have hbc : Cst b := cst_fr hc hbf
  refine ⟨by simpa only [DS.set_env_self] using hbv, hbi, hbr, ?_, ?_⟩
  · exact Cst.of_fr (T := [x]) hbc (Fr.set _ _ (by simp))
      (by simpa only [List.mem_singleton, not_or] using
        ⟨Ne.symm hxc.1, Ne.symm hxc.2.1, Ne.symm hxc.2.2⟩)
  · exact Fr.trans (Fr.weaken hbf (by intro y hy; exact List.mem_cons_of_mem _ hy))
      (Fr.set _ _ (by simp))

/-- `lem:print`, paper/paper.tex: the packet width is
retained outside all record-reader and output scratch variables. -/
def widthVar : Fin VV := ⟨66, by decide⟩

/-- `lem:print`, paper/paper.tex: width, modulus and
entry count are read from a literal three-field internal header. -/
def packetFields : St VV MM :=
  .seq (readVariable widthVar) (.seq (readVariable modulusVar) (readVariable countVar))

/-- `lem:print`, paper/paper.tex: exact field decoding
locates the start of the native record table and retains every field. -/
theorem packetFields_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (width q count : ℕ) (rest : List Bool)
    (hin : C.inp.drop a.ip = natWord width ++ natWord q ++ natWord count ++ rest)
    (hw : natBitLength width + 2 ≤ C.Wd)
    (hq : natBitLength q + 2 ≤ C.Wd)
    (hn : natBitLength count + 2 ≤ C.Wd) :
    Hs C packetFields a
      (30 * natBitLength width + 30 * natBitLength q + 30 * natBitLength count + 98)
      (fun b => b.env widthVar = width ∧ b.env modulusVar = q ∧ b.env countVar = count ∧
        b.ip = a.ip + (natWord width ++ natWord q ++ natWord count).length ∧
        b.out = a.out ∧ Cst b) := by
  unfold packetFields
  refine (Hs.seq (t2 := 30 * natBitLength q + 30 * natBitLength count + 65)
    (readVariable_spec C a hc widthVar (by decide) (by decide) width _
      (by simpa only [List.append_assoc] using hin) hw)
    fun b ⟨hbw, hbi, hbr, hbc, _⟩ => ?_).mono (by omega) (fun _ h => h)
  have hbin : C.inp.drop b.ip = natWord q ++ natWord count ++ rest := by
    rw [hbi, ← List.drop_drop, hin]
    simp only [List.append_assoc, List.drop_left]
  refine (Hs.seq (t2 := 30 * natBitLength count + 32)
    (readVariable_spec C b hbc modulusVar (by decide) (by decide) q _
      (by simpa only [List.append_assoc] using hbin) hq)
    fun d ⟨hdq, hdi, hdr, hdc, hdf⟩ => ?_).mono (by omega) (fun _ h => h)
  have hdin : C.inp.drop d.ip = natWord count ++ rest := by
    rw [hdi, ← List.drop_drop, hbin]
    simp only [List.append_assoc, List.drop_left]
  refine (readVariable_spec C d hdc countVar (by decide) (by decide) count _ hdin hn).mono le_rfl ?_
  rintro e ⟨hen, hei, her, hec, hef⟩
  refine ⟨?_, ?_, hen, ?_, ?_, hec⟩
  · rw [hef _ (by decide), hdf _ (by decide), hbw]
  · rw [hef _ (by decide), hdq]
  · rw [hei, hdi, hbi]
    simp [List.length_append, Nat.add_assoc]
  · have heo := congrArg Prod.fst her
    have hdo := congrArg Prod.fst hdr
    have hbo := congrArg Prod.fst hbr
    exact heo.trans (hdo.trans hbo)

end NearQuarticWires.StageRecovery
