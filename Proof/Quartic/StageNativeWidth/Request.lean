import Proof.Quartic.StageNativeWidth.SourceFit
import Proof.Quartic.StageNativeWidth.PackedFit
import Proof.Quartic.StagePrintTuple.Request

set_option autoImplicit false

namespace NearQuarticWires.StageNativeWidth

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5
open NearCubicGates.Close.TabMachine NearCubicGates.Close.Tabulator NearCubicGates.Close.WordPrograms
open StagePrint.NativeWidth

theorem packedBits_pos (L s D cbits : ℕ) : 1 ≤ packedBits L s D cbits := by
  unfold packedBits
  omega

theorem packedBits_source (L s D cbits : ℕ) : L ≤ packedBits L s D cbits := by
  have hm : L+s+D+4 ≤ (D+2)*(L+s+D+4) := Nat.le_mul_of_pos_left _ (by omega)
  have hx := Nat.le_max_right cbits ((D+2)*(L+s+D+4))
  unfold packedBits
  omega

theorem packedBits_coefficient (L s D cbits : ℕ) : cbits ≤ packedBits L s D cbits := by
  have h := Nat.le_max_left cbits ((D+2)*(L+s+D+4))
  unfold packedBits
  omega

/-- `lem:print`, paper/paper.tex: construct the
existing actual native tuple/cut request at the literal proposed width,
from only the original context and actual Terms coefficient/degree bounds. -/
def termCutRequest (r : StageTuple.RowContext)
    (terms : Terms (17*(Builder.allGates r.header.call).length)) (D cbits : ℕ)
    (hnodup : (Terms.keys terms).Nodup)
    (hdegree : ∀ S ∈ Terms.keys terms, S.card ≤ D)
    (hcoeff : ∀ t ∈ terms, t.2.natAbs < 2^cbits) : StageTuple.TermCutRequest where
  toRowContext := r
  terms := terms
  stackWidth := packedBits r.nativeFieldWidth (2 * PrimT.C4Geo.width r.header.prepared.starParams) D cbits
  degree := D
  width_pos := packedBits_pos _ _ _ _
  terms_nodup := hnodup
  terms_degree := hdegree
  row_width_le := (packedBits_source r.nativeFieldWidth (2 * PrimT.C4Geo.width r.header.prepared.starParams) D cbits).trans (by omega)
  fields_fit := by
    intro i row hr z hz
    exact (kids_fit r i row hr z hz).trans_le
      (Nat.pow_le_pow_right (by decide) ((packedBits_source r.nativeFieldWidth (2 * PrimT.C4Geo.width r.header.prepared.starParams) D cbits).trans (by omega)))
  coefficient_fit := by
    intro t ht
    exact SInt.encS_lt ((hcoeff t ht).trans_le
      (Nat.pow_le_pow_right (by decide) (packedBits_coefficient r.nativeFieldWidth (2 * PrimT.C4Geo.width r.header.prepared.starParams) D cbits)))
  stack_fit := by
    intro t ht rows hrows
    have hlen : rows.length = t.1.card := by
      simpa only [List.length_map, Finset.length_sort] using mem_tuples_length _ rows hrows
    have hrow : ∀ row ∈ rows, row.length = 2 * PrimT.C4Geo.width r.header.prepared.starParams + 1 ∧
        ∀ z ∈ row, SInt.encS z < 2^r.nativeFieldWidth := by
      intro row hr
      obtain ⟨pool, hp, hmem⟩ := mem_tuples_mem _ rows hrows row hr
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hp
      exact ⟨r.nativeKids_row_length i row hmem, kids_fit r i row hmem⟩
    have hd : rows.length ≤ D := by rw [hlen]; exact hdegree t.1 (List.mem_map_of_mem ht)
    have hf := packed_fits r.nativeFieldWidth
      (2 * PrimT.C4Geo.width r.header.prepared.starParams) D cbits rows t.2 hd hrow (hcoeff t ht)
    simpa only [hlen] using hf.1

end NearQuarticWires.StageNativeWidth
