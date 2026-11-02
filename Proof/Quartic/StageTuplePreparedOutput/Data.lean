import Proof.Quartic.StageTuplePreparedOutput.Caches
import Proof.Quartic.StageNativeWidth.Polynomial
import Proof.Gates.Dispatch.ParamsF

set_option autoImplicit false

namespace NearQuarticWires.StageTuplePreparedOutput

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Interfaces
open NearCubicGates.Close.Interfaces.Formats
open StageTuple

variable {ns : ℕ}

/-- `lem:print`, paper/paper.tex: the
three retained original fields use the existing nested prepared framing. -/
def prefixFields (P : Fin 10↪Fin (ns+1)) (r : TermCutRequest) : List (CacheField ns) :=
  [⟨P 0,callWord r.header.call,true⟩,
   ⟨P 1,(StagePrint.Header.baseHeaderValues r.header).flatMap natWord,true⟩,
   ⟨P 2,r.contextWord,true⟩]

/-- `lem:print`, paper/paper.tex: the
remaining genuine helper fields preserve the exact width, signed
constants, row dimension, degree and repeated nested-width bytes. -/
def suffixFields (P : Fin 10↪Fin (ns+1)) (r : TermCutRequest) : List (CacheField ns) :=
  [⟨P 4,natWord (r.stackWidth+1),false⟩,
   ⟨P 5,frame (SignedSortKey.binary (r.stackWidth+1) (SInt.encS 0)),true⟩,
   ⟨P 6,frame (SignedSortKey.binary (r.stackWidth+1) (SInt.encS 1)),true⟩,
   ⟨P 7,natWord (r.rowDimension+1),false⟩,
   ⟨P 8,natWord r.degree,false⟩,
   ⟨P 4,natWord (r.stackWidth+1),true⟩]

/-- `lem:print`, paper/paper.tex: the
original source prefix is the actual three fields before the Terms frame. -/
def originalPrefix (r : TermCutRequest) : List Bool :=
  prefixBytes (frame (callWord r.header.call))
    (frame ((StagePrint.Header.baseHeaderValues r.header).flatMap natWord)) r.contextWord

/-- `lem:print`, paper/paper.tex: the
unvisited original suffix retains the stacking width, degree and five
empty fields after the actual Terms frame. -/
def originalSuffix (r : TermCutRequest) : List Bool :=
  frame (natWord r.stackWidth)++frame (natWord r.degree)++List.replicate 5 false

/-- `lem:print`, paper/paper.tex: the
fixed source scan reaches exactly the original Terms frame. -/
theorem original_split (r : TermCutRequest) :
    r.word=originalPrefix r++frame (termsWord r.terms)++originalSuffix r := by
  have hnil : frame ([] : List Bool)=[false] := rfl
  simp [TermCutRequest.word, originalPrefix, originalSuffix, prefixBytes, Top.loadRec,
    List.replicate_succ, List.append_assoc, hnil]

/-- `prop:time`, paper/paper.tex: the
only Terms-dependent scan is a literal subword of the complete source. -/
theorem original_slice_le (r : TermCutRequest) :
    (originalPrefix r).length+(frame (termsWord r.terms)).length≤r.word.length := by
  rw [original_split, List.length_append, List.length_append]
  omega

/-- `lem:print`, paper/paper.tex: the
exact whole prepared word has one original Terms field, the nine real
cache fields in order, its final empty field and outer delimiter. -/
theorem prepared_bytes (P : Fin 10↪Fin (ns+1)) (r : TermCutRequest) :
    (prefixFields P r).flatMap CacheField.bytes++marks (frame (termsWord r.terms))++
      (suffixFields P r).flatMap CacheField.bytes++[true,false,false] = frame r.preparedWord := by
  simp [prefixFields, suffixFields, CacheField.bytes, TermCutRequest.preparedWord,
    TermCutRequest.preparedFields, CoefficientRequest.output, Top.loadRec,
    NearCubicGates.Close.Codec.frame_eq_marks, marks,
    List.append_assoc]

/-- `prop:time`, paper/paper.tex: every
actual retained cache byte reserve is linear in the separate structural
magnitude, which contains neither Terms nor the length of Terms. -/
theorem cache_reserve_le (P : Fin 10↪Fin (ns+1)) (r : TermCutRequest) :
    cachesReserve (prefixFields P r)+cachesReserve (suffixFields P r) ≤
      100*r.setupStructuralMagnitude := by
  have hw : natBitLength (r.stackWidth+1)≤r.stackWidth+2 :=
    NearCubicGates.Close.Dispatch.natBitLength_le_succ _
  have hd := (StageNativeWidth.nativeDimensions_le r.toRowContext).1
  have hr : natBitLength (r.rowDimension+1)≤2*r.header.call.n+2 := by
    have h := NearCubicGates.Close.Dispatch.natBitLength_le_succ (r.rowDimension+1)
    unfold TermCutRequest.rowDimension at h ⊢
    omega
  have hdeg := NearCubicGates.Close.Dispatch.natWord_length r.degree
  simp only [cachesReserve, prefixFields, suffixFields, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, CacheField.reserve, frame_length,
    SignedSortKey.binary_length, NearCubicGates.Close.Dispatch.natWord_length]
  unfold TermCutRequest.setupStructuralMagnitude
  omega

end NearQuarticWires.StageTuplePreparedOutput
