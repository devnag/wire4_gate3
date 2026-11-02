import Proof.Quartic.StageGreedyNativeData.Values

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyNativeData

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5
open NearCubicGates.Close.TabMachine NearCubicGates.Close.Interfaces
open StagePrint

theorem original_count {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    2^PrimT.C4Geo.dRow (GreedyCollector.star r)*
      2^PrimT.C4Geo.dR (GreedyCollector.star r)=r.child.cellCall.ncol :=
  StageNativeMeaning.nativePrefix_count
    (GreedyEntry.Request.rowContext ⟨r,⟨0,StageLiftSourceCost.walkCount_pos r⟩⟩)

/-- `imp:partition`, `lem:residue` and `lem:print`,
paper/paper.tex: the
actual centered native prefix is exactly the original recovered-count
table, including odd-dimensional padding and every bad witness. -/
theorem centered_prefix {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    ((pvals false (cutTable (table r).matrix)).take r.child.cellCall.ncol).map
      (Walks.centeredResidue (r.prime^r.child.selected.1.e : ℕ))=Greedy.printTable r := by
  let U:=2^PrimT.C4Geo.dRow (GreedyCollector.star r)
  let C:=2^PrimT.C4Geo.dR (GreedyCollector.star r)
  have hC : C ≤ U := Nat.pow_le_pow_right (by decide) (GreedyCollector.star r).centerBits_balanced.1
  let f : Fin (U*C)→ℤ := fun z=>Greedy.recoveredCountOf r.child.cellCall
    (Greedy.splitWeight r.child.cellCall r.child.seedPrefix r.sign)
    (z.cast (original_count r)) r.pattern r.prime r.digits r.residues
  have hh:=native_square_prefix_centers U C hC
    (fun high low=>Walks.centeredResidue (r.prime^r.child.selected.1.e : ℕ)
      (cutTable (table r).matrix high low)) f (by
      intro high low
      have hv:=table_center_modEq r high low
      have he:=StageRecovery.centeredResidue_of_emod_eq _ _ _ hv
      exact he)
  have hpvals : pvals false (fun high low : Fin U=>
      Walks.centeredResidue (r.prime^r.child.selected.1.e : ℕ)
        (cutTable (table r).matrix high low))=
      (pvals false (cutTable (table r).matrix)).map
        (Walks.centeredResidue (r.prime^r.child.selected.1.e : ℕ)) := by
    simp only [pvals,Bool.false_eq_true,if_false,List.map_flatten,List.map_ofFn,Function.comp_def]
    rfl
  rw [hpvals,←List.map_take] at hh
  have hf : List.ofFn f=Greedy.printTable r := by
    unfold Greedy.printTable
    apply (List.ofFn_congr (original_count r) f).trans
    apply congrArg List.ofFn
    funext z
    change Greedy.recoveredCountOf _ _ ((z.cast (original_count r).symm).cast (original_count r)) _ _ _ _=_
    congr 1
  rw [hf] at hh
  have hcount : U*C=r.child.cellCall.ncol := original_count r
  rwa [hcount] at hh

theorem tableNaturals_cast {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    (StageRecovery.tableNaturals (table r)).map (fun n : ℕ=>(n : ℤ))=
      pvals false (cutTable (table r).matrix) := by
  unfold StageRecovery.tableNaturals
  rw [List.map_map]
  conv_rhs=>rw [←List.map_id (pvals false (cutTable (table r).matrix))]
  apply List.map_congr_left
  intro value hv
  obtain ⟨high,low,rfl⟩:=StageRecovery.mem_pvals_false _ value hv
  exact Int.toNat_of_nonneg (StageRecovery.cutTable_nonneg _ (table_nonnegative r) high low)

/-- `lem:print` and `lem:residue`, paper/paper.tex: the actual nonnegative native packet
decodes to the canonical integer codec of the original printTable. -/
theorem native_output {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    (nativeRequest r).output=listWord NearCubicGates.Close.Interfaces.intWord (Greedy.printTable r) := by
  change listWord NearCubicGates.Close.Interfaces.intWord ((StageRecovery.tableNaturals (table r)).take r.child.cellCall.ncol |>.map
    (fun n : ℕ=>Walks.centeredResidue (r.prime^r.child.selected.1.e : ℕ) (n : ℤ)))=_
  apply congrArg (listWord NearCubicGates.Close.Interfaces.intWord)
  have h:=congrArg (fun xs : List ℤ=>
    (xs.take r.child.cellCall.ncol).map (Walks.centeredResidue (r.prime^r.child.selected.1.e : ℕ)))
    (tableNaturals_cast r)
  simpa only [←List.map_take,List.map_map,Function.comp_def,centered_prefix] using h

end NearQuarticWires.StageGreedyNativeData
