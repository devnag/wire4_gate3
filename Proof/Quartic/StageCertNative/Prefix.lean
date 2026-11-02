import Proof.Quartic.StageCertNative.Value
import Proof.Quartic.StageNativeMeaning.Prefix

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5
open NearCubicGates.Close.TabMachine
open StageCertificateControl StageCert.Tokens StageCertTests

/-- `imp:partition` and `lem:print`, paper/paper.tex: the actual padded native square contains between one
and two complete original-center populations. -/
theorem actualTable_count {B1 B2 : ℕ} (r : IndexedRequest B1 B2) :
    2^(r.prepared.call.n-r.prepared.selected.1.k)≤(actualTable r).count ∧
      (actualTable r).count≤2*2^(r.prepared.call.n-r.prepared.selected.1.k) := by
  have hs:=(zeroMoment r).rules
  have hc:=Builder.centerCount_eq r.prepared.call hs
  have hb:=hs.starParams.centerBits_balanced
  change PrimT.C4Geo.dR hs.starParams≤PrimT.C4Geo.dRow hs.starParams ∧
    PrimT.C4Geo.dRow hs.starParams≤PrimT.C4Geo.dR hs.starParams+1 at hb
  change r.prepared.call.n-r.prepared.selected.1.k=
    PrimT.C4Geo.dRow hs.starParams+PrimT.C4Geo.dR hs.starParams at hc
  change 2^(r.prepared.call.n-r.prepared.selected.1.k)≤
      2^PrimT.C4Geo.dRow hs.starParams*2^PrimT.C4Geo.dRow hs.starParams ∧
    2^PrimT.C4Geo.dRow hs.starParams*2^PrimT.C4Geo.dRow hs.starParams≤
      2*2^(r.prepared.call.n-r.prepared.selected.1.k)
  rw [←pow_add]
  constructor
  · exact Nat.pow_le_pow_right (by decide) (by omega)
  · have he:=Nat.pow_le_pow_right (n:=2) (by decide : 0<2)
      (show PrimT.C4Geo.dRow hs.starParams+PrimT.C4Geo.dRow hs.starParams≤
        r.prepared.call.n-r.prepared.selected.1.k+1 by omega)
    simpa only [pow_succ,Nat.mul_comm] using he

/-- `imp:partition`, `imp:pullback` and `lem:print`, paper/paper.tex: cropping the ACTUAL signed
native table at the original center count yields the literal complete
population/digit/final moment sequence, in original Builder order.
No good-witness, good-column or replacement-table premise occurs. -/
theorem actualTable_prefix {B1 B2 : ℕ} (r : IndexedRequest B1 B2) :
    (nativeSignedRequest (actualTable r)).values.take
      (2^(r.prepared.call.n-r.prepared.selected.1.k))=
      List.ofFn (fun z : Fin (2^(r.prepared.call.n-r.prepared.selected.1.k))=>
        (actualTestTable r.prepared.call (zeroMoment r).rules r.prepared.witness
          (actualOrdinal r).kind z).1) := by
  let hs:=(zeroMoment r).rules
  let U:=2^PrimT.C4Geo.dRow hs.starParams
  let C:=2^PrimT.C4Geo.dR hs.starParams
  have hC : C≤U := Nat.pow_le_pow_right (by decide) hs.starParams.centerBits_balanced.1
  have hc : U*C=2^(r.prepared.call.n-r.prepared.selected.1.k) :=
    StageNativeMeaning.nativePrefix_count (zeroMoment r).nativeContext
  let f : Fin (U*C)→ℤ := fun z=>
    (actualTestTable r.prepared.call hs r.prepared.witness (actualOrdinal r).kind
      ⟨z.val,by
        change z.val<2^(r.prepared.call.n-r.prepared.selected.1.k)
        rw [←hc];exact z.isLt⟩).1
  have hp:=StagePrint.native_square_prefix_centers U C hC
    (StagePrint.cutTable (actualTable r).matrix) f (by
      intro high low
      change StagePrint.cutTable (actualTable r).matrix (high.castLE hC) low=_
      rw [actualTable_value]
      have hm:=(zeroMoment r).nativeTermValue_sum_eq_actualTestTable high low
      change (∑i : Fin (termCount r),(actualMoment r i).nativeTermValue high.val low.val)=
        (actualTestTable r.prepared.call hs r.prepared.witness (actualOrdinal r).kind
          (StagePrint.centerIndex r.prepared.call hs low high)).1 at hm
      exact hm)
  change (pvals false (StagePrint.cutTable (actualTable r).matrix)).take _=_
  have hp' := hp
  simp only [hc,f,Fin.val_cast,Fin.eta] at hp'
  dsimp only [hs,zeroMoment,actualMoment] at hp' ⊢
  exact hp'

end NearQuarticWires.StageCertNative
