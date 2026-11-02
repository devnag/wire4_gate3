import Proof.Quartic.StageCertificateControl.CertificateFamily
import Proof.Quartic.StageCertificateControl.BatchedMachine

/-!
# The actual all-calls batch of indexed whole certificate tables

Paper: Step 2 of `sec:algorithm`, paper/paper.tex,
`lem:print`, and `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Interfaces

/-- `sec:algorithm` and `lem:print`, paper/paper.tex: each indexed native payload contains the actual
binary threshold followed by the unchanged complete native record body. -/
noncomputable def indexedNativePayload {B1 B2 : ℕ} (payload : IndexedRequest B1 B2→List Bool)
    (r : IndexedRequest B1 B2) : List Bool :=
  RepairRepresentation.natWord r.metadata.threshold++payload r

/-- `sec:algorithm`, paper/paper.tex: the complete
batch retains the original prep once, writes the actual test count,
and concatenates every complete indexed payload in its original order. -/
noncomputable def certificateBatchWord (B1 B2 : ℕ) (payload : IndexedRequest B1 B2→List Bool)
    (r : Call×List Bool) : List Bool :=
  let F := certificatePoolFamily B1 B2 r
  flattenedPoolWord F.source (F.caches (indexedNativePayload payload)) F.count

/-- `prop:time`, paper/paper.tex: the actual
complete batch budget includes count computation, cold index/threshold
work, every real whole-table call, and the single final flattening pass. -/
noncomputable def certificateBatchBudget (B1 B2 : ℕ) (payload : IndexedRequest B1 B2→List Bool)
    (baseBudget : IndexedRequest B1 B2→ℕ) (r : Call×List Bool) : ℕ :=
  batchedMachineBudget (certificatePoolFamily B1 B2 r) (indexedNativePayload payload)
    (indexedNativeBudget baseBudget) (countHeaderBudget B1 B2 r)

/-- `sec:algorithm`, `lem:print`, and `prop:time`, paper/paper.tex: the actual original
preparation is retained once, its count is physically computed, and a
single fixed indexed program calls every whole native table. The real
count bank is included in the physical allocator, all default families
are empty, and every native byte is copied unchanged. -/
noncomputable def certificateBatchWordFunction (B1 B2 : ℕ)
    {payload : IndexedRequest B1 B2→List Bool} {baseBudget : IndexedRequest B1 B2→ℕ}
    (base : WordFunction (IndexedRequest B1 B2) IndexedRequest.baseWord
      (fun r => frame (payload r)) baseBudget) :
    WordFunction (Call×List Bool) (countWord B1 B2)
      (fun r => frame (certificateBatchWord B1 B2 payload r)) (certificateBatchBudget B1 B2 payload baseBudget) := by
  let counter := countWordFunction B1 B2
  let indexed := indexedNativeWordFunction B1 B2 base
  let provider := extendedBankWordFunction indexed counter.program.tapeCount
  have hq : counter.program.tapeCount≤provider.program.tapeCount := by
    change counter.program.tapeCount≤ indexed.program.tapeCount+counter.program.tapeCount
    omega
  exact batchedTablesWordFunction counter provider hq (certificatePoolFamily B1 B2)
    (certificatePoolFamily_source B1 B2) (certificatePoolFamily_count B1 B2)

end NearQuarticWires.StageCertificateControl
