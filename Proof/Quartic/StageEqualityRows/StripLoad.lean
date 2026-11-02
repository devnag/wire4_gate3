import Proof.Quartic.StageEqualityRows.StripBounds

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageEqualityRows

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Expand.PolyTab
open StagePrint

def stripStart (r : NativeStreamRequest) : WState 15 24 :=
  idealStart 15 24 (temporaryWord r) (fun _=>0)
def stripLoaded (r : NativeStreamRequest) : WState 15 24 :=
  ((stripStart r).sets 1 (temporaryWord r)).seth 0 (2*(temporaryWord r).length+1)
def leadingNaturals (r : NativeStreamRequest) : List ℕ := [width r,r.fieldWidth+1,2*r.cuts.length]
def leadingWord (r : NativeStreamRequest) : List Bool := (leadingNaturals r).flatMap natWord

def afterLeading (r : NativeStreamRequest) : WState 15 24 :=
  (stripLoaded r).seth 1 (leadingWord r).length

def widthRead (r : NativeStreamRequest) : WState 15 24 :=
  ((afterLeading r).seth 1 ((leadingWord r).length+(natWord (width r)).length)).setv 14 (width r)

/-- `lem:print`, paper/paper.tex: the actual
framed temporary request is physically loaded onto a raw source tape. -/
theorem stripLoaded_run (r : NativeStreamRequest) :
    WExec (stripCapacity r) (StageGamma.unframeRecord 0 1 20) (stripStart r) (stripLoaded r)
      (23*(temporaryWord r).length+5) := by
  have e:=StageGamma.unframeRecord_run (stripCapacity r) (0 : Fin 16) 1 (by decide) 20
    (temporaryWord r) [] [] (stripStart r) (by simp [stripStart,idealStart]) rfl rfl rfl (temporaryWord_length_le r)
  simpa [stripLoaded,stripStart,idealStart] using e

/-- `lem:print`, paper/paper.tex: the first
three encoded metadata fields are skipped from their actual bits;
the potentially large row count is never decoded into unary. -/
theorem afterLeading_run (r : NativeStreamRequest) :
    WExec (stripCapacity r) (skipRawNaturals 1 6 7 3) (stripLoaded r) (afterLeading r)
      (rawNaturalCost (leadingNaturals r)) := by
  have hw:=bitLength_le (width r)
  have hp:=bitLength_le (r.fieldWidth+1)
  have hg:=bitLength_le (2*r.cuts.length)
  have hsource : (stripLoaded r).st 1=leadingWord r++natWord (width r)++
      (temporaryColumns r).flatMap frame++weakStream r := by
    simp only [stripLoaded,WState.seth_st,WState.sets_st,Function.update_self,temporaryWord_shape]
    simp [temporaryNaturals,leadingWord,leadingNaturals,List.append_assoc]
  have e:=skipRawNaturals_run (stripCapacity r) (1 : Fin 16) 6 7 (by decide)
    (leadingNaturals r) [] (natWord (width r)++(temporaryColumns r).flatMap frame++weakStream r)
    (stripLoaded r) (by simpa only [List.nil_append,List.append_assoc,leadingWord] using hsource) rfl rfl rfl
    (by intro v hv;simp only [leadingNaturals,List.mem_cons,List.not_mem_nil,or_false] at hv
        rcases hv with rfl|rfl|rfl <;> unfold stripCapacity capacity <;> omega)
  simpa [leadingNaturals,afterLeading,leadingWord] using e

/-- `lem:print`, paper/paper.tex: the runtime
dense width is read from the fourth genuine natural field; all
source bytes and the other metadata remain unchanged. -/
theorem widthRead_run (r : NativeStreamRequest) :
    WExec (stripCapacity r) (readNatM false 1 6 7 14 8 9) (afterLeading r) (widthRead r)
      ((natBitLength (width r)+2)*(40*2^natBitLength (width r)+40)) := by
  have e:=readNatM_spec (stripCapacity r) false (1 : Fin 16) 6 7 14 8 9
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (width r) (leadingWord r)
    ((temporaryColumns r).flatMap frame++weakStream r) (afterLeading r)
    (by simp only [afterLeading,stripLoaded,WState.seth_st,WState.sets_st,Function.update_self,
          NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.enc,Bool.false_eq_true,ite_false,
          temporaryWord_shape]
        simp [temporaryNaturals,leadingWord,leadingNaturals,List.append_assoc])
    rfl rfl rfl rfl rfl (by simpa only [show (afterLeading r).val 14=0 from rfl,Nat.zero_add]
      using width_decode_fits r)
  simpa only [stp,Bool.false_eq_true,ite_false,Nat.one_mul,
    show (afterLeading r).val 14=0 from rfl,Nat.zero_add,widthRead] using e

end NearQuarticWires.StageEqualityRows
