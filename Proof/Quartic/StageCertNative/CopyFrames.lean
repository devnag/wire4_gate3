import Proof.Quartic.StageCertNative.CopyFrame
import Proof.Quartic.StagePrint.ContextTarget

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells

def copyRawFrames : ℕ→St VV MM
  | 0=>skipS
  | n+1=>.seq copyRawFrame (copyRawFrames n)

/-- `lem:print`, paper/paper.tex: a fixed
number of exact source fields is copied by its literal frame markers,
including empty fields, without a decoded source-length premise. -/
theorem copyRawFrames_run (C : Ctx) (fields : List (List Bool)) (rest : List Bool)
    (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip=fields.flatMap frame++rest) :
    Hs C (copyRawFrames fields.length) a
      (11*(fields.map List.length).sum+8*fields.length+1) (fun z=>
      z.ip=a.ip+(fields.flatMap frame).length ∧ z.out=a.out++fields.flatMap frame ∧
      (z.ram,z.rc,z.kin,z.kout,z.kc)=(a.ram,a.rc,a.kin,a.kout,a.kc) ∧
      Cst z ∧ Fr a z [t0,vJ]) := by
  induction fields generalizing a with
  | nil=>
    refine (skip_spec a).mono (by simp) ?_
    rintro z rfl
    refine ⟨by simp [DS.set],by simp [DS.set],rfl,?_,Fr.set a _ (by simp)⟩
    exact Cst.of_fr hc (Fr.set (T:=[vJ]) a 0 (by simp)) (by decide)
  | cons bits fields ih=>
    unfold copyRawFrames
    apply Hx.hs
    refine Hs.then (copyRawFrame_run C bits (fields.flatMap frame++rest) a hc
      (by simpa only [List.flatMap_cons,List.append_assoc] using hin))
      (fun b ⟨bi,bo,bs,bc,bf⟩ n1 hn1=>?_)
    have bin : C.inp.drop b.ip=fields.flatMap frame++rest := by
      rw [bi,←List.drop_drop,hin,List.flatMap_cons,List.append_assoc]
      exact List.drop_left
    refine Hs.last (ih b bc bin) (fun z ⟨zi,zo,zs,zc,zf⟩ n2 hn2=>?_)
    refine ⟨⟨?_,?_,zs.trans bs,zc,(bf.weaken (by simp)).trans zf⟩,?_⟩
    · rw [zi,bi]
      simp only [List.flatMap_cons,List.length_append]
      omega
    · rw [zo,bo,List.flatMap_cons,List.append_assoc]
    · simp only [List.map_cons,List.sum_cons,List.length_cons]
      omega

/-- `lem:print`, paper/paper.tex: these are
the eleven actual once-computed context fields, with the original call
and affine-header frames preserved literally. -/
def contextFields {B1 B2 : ℕ} (r : StageCertTests.PreparedScheduleRequest B1 B2) :
    List (List Bool) :=
  [frame (NearCubicGates.Close.Interfaces.callWord r.call),
    frame ((StagePrint.Header.baseHeaderValues (StagePrint.Context.header r)).flatMap
      NearCubicWires.RepairRepresentation.natWord),
    StagePrint.Context.countsWord r,StagePrint.Context.geometryWord r,[],[],[],[],[],[],[]]

theorem contextFields_word {B1 B2 : ℕ} (r : StageCertTests.PreparedScheduleRequest B1 B2) :
    (contextFields r).flatMap frame=StagePrint.Context.word r := by
  rfl

/-- `lem:print`, paper/paper.tex: the original
cached context is copied as eleven physical fields; the whole context
is never supplied as decoded geometry or as an initialized bank. -/
theorem copyContext_run {B1 B2 : ℕ} (C : Ctx)
    (r : StageCertTests.PreparedScheduleRequest B1 B2) (rest : List Bool)
    (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip=StagePrint.Context.word r++rest) :
    Hs C (copyRawFrames 11) a (11*(StagePrint.Context.word r).length+100) (fun z=>
      z.ip=a.ip+(StagePrint.Context.word r).length ∧ z.out=a.out++StagePrint.Context.word r ∧
      (z.ram,z.rc,z.kin,z.kout,z.kc)=(a.ram,a.rc,a.kin,a.kout,a.kc) ∧
      Cst z ∧ Fr a z [t0,vJ]) := by
  have h:=copyRawFrames_run C (contextFields r) rest a hc (by rw [contextFields_word];exact hin)
  have allLengths : ∀ fields : List (List Bool),
      (fields.map List.length).sum≤(fields.flatMap frame).length := by
    intro fields
    induction fields with
    | nil=>simp
    | cons bits fields ih=>
      simp only [List.map_cons,List.sum_cons,List.flatMap_cons,List.length_append,frame_length]
      omega
  have hlen : ((contextFields r).map List.length).sum≤(StagePrint.Context.word r).length := by
    rw [←contextFields_word]
    exact allLengths _
  exact h.mono (by change 11*((contextFields r).map List.length).sum+8*11+1≤_;omega)
    (by intro z hz;simpa only [contextFields_word] using hz)

end NearQuarticWires.StageCertNative
