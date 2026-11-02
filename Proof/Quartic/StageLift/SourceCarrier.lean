import Proof.Quartic.StageLift.CachedRequest
import Proof.Quartic.StageLift.TupleResidue
import Proof.Quartic.StageLift.GammaWalk
import Proof.Quartic.StageFormulaMetadata.Packet

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats

/-- Step 3 and `lem:print`, paper/paper.tex: the exact original walk formula has its requested
Gamma split, eight actual masks and normalized original residue targets. -/
noncomputable def sourceWalkFormula {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2)
    (index : Fin (r.child.cellCall.seed.N ^ 8)) : Formula (17 * (Builder.allGates r.child.call).length) :=
  let hs := Cells.prepare_spec _ r.child.selected.1 r.child.selected.2
  let walk := printWalkAt r.child.cellCall.seed.N index
  tupleResidueWalkFormula r.child.call hs r.child.witness walk r.pattern r.prime
    (fun j row => r.digits j row % (r.prime ^ r.child.selected.1.e : ℤ))
    (fun j => r.residues j % (r.prime ^ r.child.selected.1.e : ℤ))
    (Greedy.splitWeight r.child.cellCall r.child.seedPrefix r.sign walk)

/-- `lem:print`, paper/paper.tex: one generated
walk payload uses the sole shared packet type and canonical token codec. -/
noncomputable def sourceWalkPacket {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2)
    (index : Fin (r.child.cellCall.seed.N ^ 8)) : StageFormulaMetadata.RawWalkPacket where
  index := index.val
  degree := residueDegreeBound r.child.selected.1 r.prime
  modulus := r.prime ^ r.child.selected.1.e
  arity := 17 * (Builder.allGates r.child.call).length
  payload := (toks (sourceWalkFormula r index)).flatMap tokWord

/-- Step 3 and `lem:print`, paper/paper.tex: the exact source stream retains every original walk
in its original low-first index order, including zero Gamma weights. -/
noncomputable def sourcePacketPrefix {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2)
    (count : ℕ) : List Bool :=
  ((List.ofFn (sourceWalkPacket r)).take count).flatMap StageFormulaMetadata.RawWalkPacket.word

/-- Step 3 and `lem:print`, paper/paper.tex: one actual original walk appends exactly one unchanged
four-field raw Formula packet to the source prefix. -/
theorem sourcePacketPrefix_succ {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2)
    (count : ℕ) (hcount : count < r.child.cellCall.seed.N ^ 8) :
    sourcePacketPrefix r (count + 1) = sourcePacketPrefix r count ++
      (sourceWalkPacket r ⟨count, hcount⟩).word := by
  unfold sourcePacketPrefix
  rw [List.take_succ_eq_append_getElem (by simpa only [List.length_ofFn] using hcount),
    List.flatMap_append, List.flatMap_singleton, List.getElem_ofFn]

/-- Step 3 and `lem:print`, paper/paper.tex: the finite cached word is exactly the original
preparation-stage output for this actual dispatched print request. -/
theorem preparedWordOf_eq_prepWord {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    preparedWordOf r = Program.prepWord B1 B2 r.child.call r.child.witness := by
  have h := printInput_preparedPrefix r
  have heq : Program.prepWord B1 B2 r.child.call r.child.witness ++
        Greedy.gammaTableWord r.child ++ Greedy.printIndexWord r =
      preparedWordOf r ++ Greedy.gammaTableWord r.child ++ Greedy.printIndexWord r := by
    simpa only [Greedy.printInput, preparedWordOf, StageMain.Compact.compactInput,
      List.append_assoc] using h
  exact (List.append_cancel_right (List.append_cancel_right heq)).symm

/-- Step 3 and `lem:print`, paper/paper.tex: a single raw preparation context precedes the
physically counted original-walk stream; no Gamma table is copied. -/
noncomputable def sourceCarrierWord {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) : List Bool :=
  natWord (preparedWordOf r).length ++ preparedWordOf r ++
    natWord (r.child.cellCall.seed.N ^ 8) ++ sourcePacketPrefix r (r.child.cellCall.seed.N ^ 8)

/-- Step 3 and `lem:print`, paper/paper.tex: the source carrier's literal bytes agree with the
original preparation word and unchanged shared raw walk packets. -/
theorem sourceCarrierWord_layout {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    sourceCarrierWord r =
      natWord (Program.prepWord B1 B2 r.child.call r.child.witness).length ++
        Program.prepWord B1 B2 r.child.call r.child.witness ++
          natWord (r.child.cellCall.seed.N ^ 8) ++
            (List.ofFn (sourceWalkPacket r)).flatMap StageFormulaMetadata.RawWalkPacket.word := by
  have ht : (List.ofFn (sourceWalkPacket r)).take (r.child.cellCall.seed.N ^ 8) =
      List.ofFn (sourceWalkPacket r) := List.take_of_length_le (by simp)
  simp only [sourceCarrierWord, preparedWordOf_eq_prepWord, sourcePacketPrefix, ht]

end NearQuarticWires.StageLift
