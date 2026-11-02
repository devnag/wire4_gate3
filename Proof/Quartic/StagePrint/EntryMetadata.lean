import Proof.Quartic.StagePrint.EntryContextRead
import Proof.Quartic.StagePrint.EntryCoefficientBits
import Proof.Quartic.StageRecovery.PacketFields

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint.EntryFormat
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells

/-- `lem:print`, paper/paper.tex: one actual
compiled entry retains its original low-first ordinal, degree and
coefficient scale by binary-codec reads. -/
def readEntryFields : St VV MM :=
  .seq (StageRecovery.readVariable indexVar)
  (.seq (StageRecovery.readVariable GreedyEntry.degreeVar)
    (StageRecovery.readVariable GreedyEntry.modulusVar))

/-- `lem:print`, paper/paper.tex: the exact
three-field parser consumes only the finite header and preserves the
retained source context and complete following Terms frame. -/
theorem readEntryFields_run (C : Ctx) (index D scale : ℕ) (rest : List Bool)
    (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip=natWord index++natWord D++natWord scale++rest)
    (hi : natBitLength index+2≤C.Wd) (hd : natBitLength D+2≤C.Wd)
    (hs : natBitLength scale+2≤C.Wd) :
    Hs C readEntryFields a (30*(natBitLength index+natBitLength D+natBitLength scale)+98)
      (fun z=>z.env indexVar=index ∧ z.env GreedyEntry.degreeVar=D ∧
        z.env GreedyEntry.modulusVar=scale ∧ C.inp.drop z.ip=rest ∧
        (z.out,z.ram,z.rc,z.kin,z.kout,z.kc)=(a.out,a.ram,a.rc,a.kin,a.kout,a.kc) ∧
        Cst z ∧ Fr a z ([indexVar,GreedyEntry.degreeVar,GreedyEntry.modulusVar]++rdNatT)) := by
  unfold readEntryFields
  refine (Hs.seq (t2:=30*natBitLength D+30*natBitLength scale+65)
    (StageRecovery.readVariable_spec C a hc indexVar (by decide) (by decide) index _
      (by simpa only [List.append_assoc] using hin) hi)
    fun b ⟨bi,bip,brest,bc,bfr⟩=>?_).mono (by omega) (fun _ h=>h)
  have bin : C.inp.drop b.ip=natWord D++natWord scale++rest := by
    rw [bip,←List.drop_drop,hin]
    simp only [List.append_assoc,List.drop_left]
  refine (Hs.seq (t2:=30*natBitLength scale+32)
    (StageRecovery.readVariable_spec C b bc GreedyEntry.degreeVar (by decide) (by decide)
      D _ (by simpa only [List.append_assoc] using bin) hd)
    fun d ⟨dd,dip,drest,dc,dfr⟩=>?_).mono (by omega) (fun _ h=>h)
  have din : C.inp.drop d.ip=natWord scale++rest := by
    rw [dip,←List.drop_drop,bin]
    simp only [List.append_assoc,List.drop_left]
  refine (StageRecovery.readVariable_spec C d dc GreedyEntry.modulusVar (by decide) (by decide)
    scale _ din hs).mono le_rfl ?_
  rintro z ⟨zs,zip,zrest,zc,zfr⟩
  have zram : z.ram=a.ram :=
    (congrArg (fun t=>t.2.1) zrest).trans ((congrArg (fun t=>t.2.1) drest).trans
      (congrArg (fun t=>t.2.1) brest))
  have zrc : z.rc=a.rc :=
    (congrArg (fun t=>t.2.2.1) zrest).trans ((congrArg (fun t=>t.2.2.1) drest).trans
      (congrArg (fun t=>t.2.2.1) brest))
  refine ⟨?_,?_,zs,?_,?_,zc,?_⟩
  · rw [zfr _ (by decide),dfr _ (by decide),bi]
  · rw [zfr _ (by decide),dd]
  · rw [zip];exact drop_adv din
  · refine Prod.ext ?_ (Prod.ext zram (Prod.ext zrc ?_))
    · exact (congrArg Prod.fst zrest).trans ((congrArg Prod.fst drest).trans (congrArg Prod.fst brest))
    · exact (congrArg (fun t=>t.2.2.2) zrest).trans
        ((congrArg (fun t=>t.2.2.2) drest).trans (congrArg (fun t=>t.2.2.2) brest))
  · exact (bfr.weaken (by simp [rdNatT])).trans ((dfr.weaken (by simp [rdNatT])).trans (zfr.weaken (by simp [rdNatT])))

end NearQuarticWires.StagePrint.EntryFormat
