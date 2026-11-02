import Proof.Quartic.StageLift.SourceGuards
import Proof.Quartic.StageMain.CompactBounds

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces

/-- `lem:print`, paper/paper.tex: every binary
integer field is charged to the literal source bytes containing it. -/
theorem signed_field_bits_le (values : List ℤ) (z : ℤ) (hz : z ∈ values) :
    natBitLength z.natAbs ≤
      (listWord NearCubicGates.Close.Interfaces.intWord values).length := by
  have hfield : ∀ values : List ℤ, z ∈ values →
      (NearCubicGates.Close.Interfaces.intWord z).length ≤
      (values.flatMap NearCubicGates.Close.Interfaces.intWord).length := by
    intro values
    induction values with
    | nil => simp
    | cons v vs ih =>
      intro hm
      rcases List.mem_cons.mp hm with rfl | hm
      · simp only [List.flatMap_cons, List.length_append]
        omega
      · have h := ih hm
        simp only [List.flatMap_cons, List.length_append]
        omega
  have hword := hfield values hz
  have hnat := NearCubicGates.Close.Dispatch.natBitLength_le_len z.natAbs
  simp only [listWord, NearCubicGates.Close.Interfaces.intWord, List.length_append] at *
  omega

/-- `lem:print` and `prop:time`, paper/paper.tex: arbitrary raw digit and score magnitudes enter only
the once-paid index-word processing bound, never source allocation. -/
theorem raw_print_index_bits {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    ∀ z ∈ printDigitList r ++ printResidueList r,
      natBitLength z.natAbs ≤ (Greedy.printIndexWord r).length := by
  intro z hz
  have hl := congrArg List.length (printIndexWord_layout r)
  simp only [List.length_append] at hl
  rcases List.mem_append.mp hz with hz | hz
  · have h := signed_field_bits_le (printDigitList r) z hz
    omega
  · have h := signed_field_bits_le (printResidueList r) z hz
    omega

end NearQuarticWires.StageLift
