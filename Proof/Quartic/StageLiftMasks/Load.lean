import Proof.Quartic.StageLiftMasks.Setup

/-!
# Actual loaded structural factor

`def:mask` and `lem:print`, paper/paper.tex: each original edge obtains its Boolean factor from
the actual cold structural machine and retains the unchanged source
state needed for the remaining seven edges.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageLiftMasks
open NearCubicGates.Close.Cells StageLift StageCert.Tokens StageMain.Compact

noncomputable def edgeLoadCost {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) (L B : ℕ) : ℕ :=
  9*(preparedWordOf r).length+80*(sourceEnvelope r+1)+L+B+300

def edgeStructural (edge : Fin 8) : St VV MM :=
  .seq prepareEdgeSource (loadPreparedStructural edge)

theorem edgeStructural_run {B1 B2 width L B : ℕ} (input : List Bool)
    (r : Greedy.PrintRequest B1 B2) (index : Fin (r.child.cellCall.seed.N^8))
    (edge : Fin 8) (a : DS VV MM) (h : PrintMasksReady width input L B r index a) :
    Hs (structuralSourceContext B1 B2 width input L B) (edgeStructural edge) a
      (edgeLoadCost r L B) (fun b=>b.out=a.out ∧
      PrintMasksReady width input L B r index b ∧ MaskFrame a b ∧
      b.env maskStructural=(StagePrint.callStructural r.child.call
        (Cells.prepare_spec _ r.child.selected.1 r.child.selected.2) (printWalkAt _ index) edge).toNat) := by
  let C:=structuralSourceContext B1 B2 width input L B
  have hcap:=source_mask_capacity r width h.residue.width
  have hl:=structural_left_bits r index edge
  have hr:=structural_right_bits r index edge
  have hh : Hs C (edgeStructural edge) a (edgeLoadCost r L B) (fun z=>
      z.out=a.out ∧ z.kin=[] ∧ MaskFrame a z ∧ Cst z ∧
      z.env maskStructural=(StagePrint.callStructural r.child.call
        (Cells.prepare_spec _ r.child.selected.1 r.child.selected.2) (printWalkAt _ index) edge).toNat) := by
    unfold edgeStructural
    apply Hx.hs
    refine Hs.then (prepareEdgeSource_run input r index a h)
      (fun b ⟨bo,br,bf,bN,bP⟩ n1 hn1=>?_)
    refine Hs.last (loadPreparedStructural_run r index edge width input L B b br.residue.constants
      br.inputEmpty br.preparedRecords bP br.preparedCursor bN br.walkOrdinal
      (by have hw:=hcap.minWidth; omega) hcap.prepared hcap.patterns
      (lt_of_le_of_lt (Nat.add_le_add_right hl 2) hcap.patternWord)
      (lt_of_le_of_lt (Nat.add_le_add_right hr 2) hcap.patternWord)
      (br.sourceRoom edge) (br.sourceBudget edge))
      (fun z ⟨zf,zi,zo,zram,zrc,zkin,zc,zfr⟩ n2 hn2=>?_)
    have frame : MaskFrame b z := ⟨zram,fun s _=>congrFun zrc s,zi,fun x hx=>
      zfr x ((show ∀x∈maskRegisters,x∉([sourceEdgeLeft,sourceEdgeRight,patternRemaining,
        patternQuotient,patternRemainder,maskStructural,c0,t0,t3]++emitNatT) by decide) x hx)⟩
    refine ⟨⟨zo.trans bo,zkin,bf.trans frame,zc,zf⟩,?_⟩
    unfold edgeLoadCost
    omega
  obtain ⟨b,n,he,hn,bo,bkin,bf,bc,bflag⟩:=hh
  exact ⟨b,n,he,hn,bo,ready_of_frame h bc (ready_execution_valid h he) bf bkin,bf,bflag⟩

end NearQuarticWires.StageLiftMasks
