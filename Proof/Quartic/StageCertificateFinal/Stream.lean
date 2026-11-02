import Proof.Quartic.StageCertificateFinal.Requests

/-!
# The unchanged complete native batch is the literal bitmap input

Paper: `lem:print`, paper/paper.tex,
and Step 2 of `sec:algorithm`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageCertificateFinal

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Interfaces
open StageCertificateControl

/-- `lem:print`, paper/paper.tex: the base
table payload is its actual width header and unchanged signed records. -/
noncomputable def tablePayload {B1 B2 : ℕ} (tables : NativeTables B1 B2)
    (r : IndexedRequest B1 B2) : List Bool :=
  RepairRepresentation.natWord ((tables.table r).q+1)++(tables.table r).output

/-- `sec:algorithm`, paper/paper.tex: the complete
finite generated list and the physically counted cache traversal have
identical test-major bytes, with no reordering or intermediate crop. -/
theorem tests_stream {B1 B2 : ℕ} (tables : NativeTables B1 B2) (c : Call) (w : List Bool) :
    nativeTestStream (tests tables c w)=
      (List.range (certificatePoolFamily B1 B2 (c,w)).count).flatMap
        ((certificatePoolFamily B1 B2 (c,w)).caches (indexedNativePayload (tablePayload tables))) := by
  let F := certificatePoolFamily B1 B2 (c,w)
  have he : List.ofFn (fun j : Fin F.count =>
      (tableTest (F.request j).metadata.threshold (tables.table (F.request j))).word)=
      (List.range F.count).map (F.caches (indexedNativePayload (tablePayload tables))) := by
    apply List.ext_getElem
    · simp
    · intro i hi hi'
      simp only [List.length_ofFn] at hi
      simp only [List.getElem_ofFn,List.getElem_map,List.getElem_range]
      simp only [StagePrint.PoolFamily.caches,hi,dif_pos,tableTest_word,indexedNativePayload,
        tablePayload,List.append_assoc]
  change (List.ofFn (fun j : Fin F.count =>
    tableTest (F.request j).metadata.threshold (tables.table (F.request j)))).flatMap NativeTest.word=_
  have hm := List.ofFn_comp' (fun j : Fin F.count =>
    tableTest (F.request j).metadata.threshold (tables.table (F.request j))) NativeTest.word
  rw [hm] at he
  have h := congrArg List.flatten he
  simpa only [List.flatten_eq_flatMap,List.flatMap_map,Function.comp_def,id_eq] using h

/-- `sec:algorithm` and `lem:print`, paper/paper.tex: the actual all-calls counted whole-table
batch is exactly the cold bitmap request, including default calls. -/
theorem batch_eq_bitmapWord {B1 B2 : ℕ} (tables : NativeTables B1 B2) (c : Call) (w : List Bool) :
    certificateBatchWord B1 B2 (tablePayload tables) (c,w)=(bitmapRequest tables c w).word := by
  change certificateBatchWord B1 B2 (tablePayload tables) (c,w)=
    Program.prepWord B1 B2 c w++RepairRepresentation.natWord (tests tables c w).length++
      nativeTestStream (tests tables c w)
  rw [tests_count,tests_stream]
  simp only [certificateBatchWord,flattenedPoolWord,certificatePoolFamily_source,
    certificatePoolFamily_count,countWord]

end NearQuarticWires.StageCertificateFinal
