import Proof.Quartic.StageFormulaMetadata.FrameRetain

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint.GreedyEntry

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells StageFormulaMetadata

/-- `lem:print`, paper/paper.tex: retain one
actual framed field and its measured byte length in independent memory
and arithmetic locations. -/
def retainField (store : Fin MM) (lengthVar : Fin VV) : St VV MM :=
  .seq (.op (.zero payloadLengthVar))
    (.seq (readCountedFrame store) (.op (.copy lengthVar payloadLengthVar)))

/-- `lem:print`, paper/paper.tex: the reader
measures the finite field itself, preserves all following input and
pays each marker and payload bit once. -/
theorem retainField_run (C : Ctx) (store : Fin MM) (lengthVar : Fin VV)
    (hl : lengthVar∉[vZ,v1,v2,t0,t1,payloadLengthVar])
    (bits rest : List Bool) (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip=frame bits++rest)
    (hcursor : a.rc store=(a.ram store).length)
    (hfit : bits.length<2^C.Wd) :
    Hs C (retainField store lengthVar) a (10*bits.length+8) (fun b =>
      b.env lengthVar=bits.length ∧ b.env payloadLengthVar=bits.length ∧
      b.ip=a.ip+(frame bits).length ∧ b.ram store=a.ram store++bits.map Bool.toNat ∧
      b.rc store=a.rc store+bits.length ∧
      (∀ other,other≠store→b.ram other=a.ram other ∧ b.rc other=a.rc other) ∧
      (b.out,b.kin,b.kout,b.kc)=(a.out,a.kin,a.kout,a.kc) ∧
      Cst b ∧ Fr a b [t0,t1,payloadLengthVar,lengthVar]) := by
  have hlp : lengthVar≠payloadLengthVar := by intro h;subst lengthVar;exact hl (by simp)
  have hconst : vZ∉[lengthVar] ∧ v1∉[lengthVar] ∧ v2∉[lengthVar] := by
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hl
    simpa only [List.mem_singleton] using ⟨Ne.symm hl.1,Ne.symm hl.2.1,Ne.symm hl.2.2.1⟩
  unfold retainField
  refine (Hs.seq (t2:=10*bits.length+6) (hs_zero C payloadLengthVar a) fun d hd => ?_).mono
    (by omega) (fun _ h=>h)
  subst d
  let d:=a.set payloadLengthVar 0
  have hdc : Cst d:=Cst.of_fr hc (Fr.set a 0 (T:=[payloadLengthVar]) (by simp)) (by decide)
  have er:=readCountedFrame_spec C store bits rest d hdc hin hcursor
    (by simpa only [d,DS.set_env_self,Nat.zero_add] using hfit)
  refine Hs.seq (t2:=1) er fun b ⟨bl,bi,br,bcursor,bo,bstreams,bc,bfr⟩ => ?_
  have bl' : b.env payloadLengthVar=bits.length := by
    simpa only [d,DS.set_env_self,Nat.zero_add] using bl
  refine (hs_copy C lengthVar payloadLengthVar b hlp).mono le_rfl ?_
  rintro e rfl
  refine ⟨by simpa only [DS.set_env_self] using bl',?_,bi,br,bcursor,bo,bstreams,
    Cst.of_fr bc (Fr.set b _ (T:=[lengthVar]) (by simp)) hconst,?_⟩
  · simpa only [DS.set_env_ne _ _ (Ne.symm hlp)] using bl'
  · exact ((Fr.set a 0 (T:=[t0,t1,payloadLengthVar,lengthVar]) (by simp)).trans
      (bfr.weaken (by simp))).trans (Fr.set b _ (by simp))

end NearQuarticWires.StagePrint.GreedyEntry
