import Proof.Quartic.StageCertificateFinal.NativeTest
import Proof.Quartic.StageCertNative.Ordinal
import Proof.Quartic.StageCertificateControl.CertificateFamily
import Proof.Quartic.StageCertificateControl.Censuses

/-!
# Complete native table data for the exact certificate consumer

Paper: `lem:print`, paper/paper.tex,
and Step 2 of `sec:algorithm`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageCertificateFinal

open StageCertificateControl

/-- `lem:print` and `sec:algorithm`, paper/paper.tex: complete generated native tables have their
full padded census, one fixed original-arity width bound, and their
exact ordered original-column moment prefixes on every witness.
The physical word function is specified separately from these data. -/
structure NativeTables (B1 B2 : ℕ) where
  table : IndexedRequest B1 B2→StagePrint.TableRequest
  coefficient : ℕ
  degree : ℕ
  count : ∀r,(table r).count=paddedCount r.prepared.call.n r.prepared.selected.1.k
  width : ∀r,(table r).q+1≤coefficient*(r.prepared.call.n+1)^degree
  originalPrefix : ∀r,(StageCertTests.nativeSignedRequest (table r)).values.take
      (2^(r.prepared.call.n-r.prepared.selected.1.k))=
    List.ofFn (fun z : Fin (2^(r.prepared.call.n-r.prepared.selected.1.k)) =>
      (StageCertTests.actualTestTable r.prepared.call
        (Cells.prepare_spec _ r.prepared.selected.1 r.prepared.selected.2)
        r.prepared.witness (StageCertNative.actualOrdinal r).kind z).1)

end NearQuarticWires.StageCertificateFinal
