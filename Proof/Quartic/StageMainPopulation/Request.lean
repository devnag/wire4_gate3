import Proof.Quartic.StageMainMask.PopulationRequest
import Proof.Quartic.StageMainMask.StructuralFields
import Proof.Quartic.StageCert.PopulationList
import Proof.Quartic.StageOutput.PaddingDispatch

set_option autoImplicit false

namespace NearQuarticWires.StageMainPopulation

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Dispatch NearCubicGates.Close.Interfaces
open StageMainMask StageCert

def metadataFields (r : PopulationRequest) : List (Fin VV × ℕ) :=
  [(sourceWitnessIndex, r.offset), (cornerPoint 0, r.corners 0),
    (cornerPoint 1, r.corners 1), (cornerPoint 2, r.corners 2), (cornerPoint 3, r.corners 3)]

def metadataRegisters : List (Fin VV) :=
  [sourceWitnessIndex, cornerPoint 0, cornerPoint 1, cornerPoint 2, cornerPoint 3]

def metadataWord (r : PopulationRequest) : List Bool :=
  (metadataFields r).flatMap (fun f => natWord f.2)

def witnessPrefix (r : PopulationRequest) : List Bool := callWord r.call ++ metadataWord r

/-- `def:mask` and witness (W2), paper/paper.tex: the five original binary fields precede the actual
retained witness frame in the frozen population input. -/
theorem metadataWord_eq (r : PopulationRequest) :
    metadataWord r = natWord r.offset ++ (List.ofFn r.corners).flatMap natWord := by
  simp [metadataWord, metadataFields, List.ofFn_succ]

theorem request_word (r : PopulationRequest) : r.word = witnessPrefix r ++ frame r.witness := by
  simp only [PopulationRequest.word, witnessPrefix, metadataWord_eq, List.append_assoc]

theorem metadataRegisters_eq (r : PopulationRequest) :
    (metadataFields r).map Prod.fst = metadataRegisters := rfl

/-- `prop:time`, paper/paper.tex: every actual
metadata field and witness selection is bounded by the serialized input. -/
theorem encoding_bounds (r : PopulationRequest) :
    r.call.n ≤ r.word.length ∧ r.offset ≤ r.witness.length ∧
      r.witness.length ≤ r.word.length ∧
      ∀ f ∈ metadataFields r, natBitLength f.2 ≤ r.word.length := by
  have he := congrArg List.length (request_word r)
  simp only [List.length_append, NearCubicGates.Close.Dispatch.frame_length,
    witnessPrefix] at he
  refine ⟨r.arity_le_call.trans (by omega), by have h := r.selection_fits; omega, by omega, ?_⟩
  intro f hf
  have h := (natBitLength_le_len f.2).trans (StageOutput.fieldWord_length _ f hf)
  change natBitLength f.2 ≤ (metadataWord r).length at h
  omega

def firstStart : Fin VV := 180

/-- `def:mask` and witness (W2), paper/paper.tex: these are exactly the physically read selection and
four point fields, with the real source address of the witness frame. -/
structure Loaded (a : DS VV) (r : PopulationRequest) : Prop where
  corners : ∀ l, a.env (cornerPoint l) = r.corners l
  witnessBase : a.env sourceWitnessBase = (witnessPrefix r).length
  index : a.env sourceWitnessIndex = r.offset
  total : a.env populationTotal = 0

end NearQuarticWires.StageMainPopulation
