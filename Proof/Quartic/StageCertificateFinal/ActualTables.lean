import Proof.Quartic.StageCertificateFinal.Assembly
import Proof.Quartic.StageCertNative.Prefix
import Proof.Quartic.StageCertNative.Width

/-!
# The complete certificate consumer uses the actual generated native tables

Paper: `lem:print`, paper/paper.tex,
and Step 2 of `sec:algorithm`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageCertificateFinal

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5
open StageCertificateControl

/-- `imp:partition` and `lem:print`, paper/paper.tex: the actual generated table has exactly
the declared full padded native census, before the sole final crop. -/
theorem actualTable_paddedCount {B1 B2 : ℕ} (r : IndexedRequest B1 B2) :
    (StageCertNative.actualTable r).count=paddedCount r.prepared.call.n r.prepared.selected.1.k := by
  let hs:=(StageCertNative.zeroMoment r).rules
  have he:=paddedCount_exact hs.starParams
  rw [Cells.ParameterRules.star_k] at he
  change paddedCount r.prepared.call.n r.prepared.selected.1.k=
    (2^PrimT.C4Geo.dRow hs.starParams)^2 at he
  change 2^PrimT.C4Geo.dRow hs.starParams*2^PrimT.C4Geo.dRow hs.starParams=_
  simpa only [pow_two] using he.symm

/-- `lem:print` and `sec:algorithm`, paper/paper.tex: the actual source expansion and literal
all-term native construction supply every mathematical data field
of the certificate consumer, on all witnesses and padded positions. -/
noncomputable def actualTables (B1 B2 : ℕ) : NativeTables B1 B2 where
  table:=StageCertNative.actualTable
  coefficient:=StageCertNative.nativeWidthCoefficient B1
  degree:=StageCertNative.nativeWidthDegree B1
  count:=actualTable_paddedCount
  width:=by
    intro r
    exact (Nat.add_le_add_left (by decide : 1≤3) _).trans (StageCertNative.actualTable_width r)
  originalPrefix:=StageCertNative.actualTable_prefix

end NearQuarticWires.StageCertificateFinal
