import Proof.Quartic.StageLiftMasks.Request
import Proof.Quartic.StageLift.PreparedEmit

/-!
# Structural queries from the retained preparation store

`def:mask` and `lem:print`, paper/paper.tex: the actual source program reads the preparation
bytes from store nine, preserving the original index store six.
Store permutation preserves every physical instruction and its clock.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageLiftMasks
open NearCubicWires NearCubicGates.Close.Cells
open StageLift StageCert.Tokens StageMain.Compact

variable {B1 B2 : ℕ}

theorem permuteMemory_inverse {V M : ℕ} (e : Fin M≃Fin M) (a : DS V M) :
    permuteMemory e (permuteMemory e.symm a)=a := by
  cases a
  simp only [permuteMemory,Equiv.symm_symm,Equiv.apply_symm_apply]

def loadPreparedStructural (edge : Fin 8) : St VV MM :=
  permuteProgram preparedPermutation (loadEdgeStructural edge)

theorem loadPreparedStructural_run (r : Greedy.PrintRequest B1 B2)
    (index : Fin (r.child.cellCall.seed.N^8)) (edge : Fin 8)
    (width : ℕ) (input : List Bool) (L B : ℕ) (a : DS VV MM)
    (hc : Cst a) (hkin : a.kin=[])
    (hbits : a.ram preparedStore=(preparedWordOf r).map Bool.toNat)
    (hlen : a.env compactLength=(preparedWordOf r).length)
    (hcursor : a.rc preparedStore=(preparedWordOf r).length)
    (hb : a.env patternBase=r.child.selected.1.N) (hi : a.env sourceTermIndex=index.val)
    (hW : 2≤width) (hfit : (preparedWordOf r).length<2^width)
    (hNfit : 2*r.child.selected.1.N≤2^width)
    (hlfit : natBitLength (printMaskStructuralRequest r index edge).left.val+2<2^width)
    (hrfit : natBitLength (printMaskStructuralRequest r index edge).right.val+2<2^width)
    (hroom : (StageMainMask.structuralWord (printMaskStructuralRequest r index edge)).length≤L)
    (hbudget : StageMainMask.structuralBudget (printMaskStructuralRequest r index edge)≤B) :
    Hs (structuralSourceContext B1 B2 width input L B) (loadPreparedStructural edge) a
      (9*(preparedWordOf r).length+
        40*natBitLength (printMaskStructuralRequest r index edge).left.val+
        40*natBitLength (printMaskStructuralRequest r index edge).right.val+L+B+175) (fun z=>
      z.env maskStructural=(StagePrint.callStructural r.child.call
        (Cells.prepare_spec _ r.child.selected.1 r.child.selected.2) (printWalkAt _ index) edge).toNat ∧
      z.ip=a.ip ∧ z.out=a.out ∧ z.ram=a.ram ∧ z.rc=a.rc ∧ z.kin=[] ∧ Cst z ∧
      Fr a z ([sourceEdgeLeft,sourceEdgeRight,patternRemaining,patternQuotient,patternRemainder,
        maskStructural,c0,t0,t3]++emitNatT)) := by
  let old := permuteMemory preparedPermutation.symm a
  let mr := maskMomentRequest r index
  have hp : Program.prepWord B1 B2 mr.call mr.witness=preparedWordOf r :=
    (preparedWordOf_eq_prepWord r).symm
  have hc0 : Cst old := ⟨hc.z,hc.one,hc.two⟩
  have hbits0 : old.ram compactStore=(Program.prepWord B1 B2 mr.call mr.witness).map Bool.toNat := by
    rw [hp]
    simpa only [old,permuteMemory,preparedPermutation,Equiv.symm_symm,Equiv.swap_apply_left] using hbits
  have hcursor0 : old.rc compactStore=(Program.prepWord B1 B2 mr.call mr.witness).length := by
    rw [hp]
    simpa only [old,permuteMemory,preparedPermutation,Equiv.symm_symm,Equiv.swap_apply_left] using hcursor
  obtain ⟨b,n,he,hn,bflag,bi,bo,bram,brc,bkin,bc,bfr⟩ :=
    loadEdgeStructural_run mr edge width input L B old hc0 hkin hbits0
      (by rw [hp]; exact hlen) hcursor0 hb hi hW (by rw [hp]; exact hfit) hNfit
      (by simpa only [mr,maskMomentRequest_left] using hlfit)
      (by simpa only [mr,maskMomentRequest_right] using hrfit)
      (by simpa only [mr,maskMomentRequest_edge] using hroom)
      (by simpa only [mr,maskMomentRequest_edge] using hbudget)
  have hex : Ex (structuralSourceContext B1 B2 width input L B)
      (loadPreparedStructural edge) a (permuteMemory preparedPermutation b) n := by
    simpa only [loadPreparedStructural,old,permuteMemory_inverse] using
      execution_permuteMemory preparedPermutation he
  refine ⟨permuteMemory preparedPermutation b,n,hex,?_,?_,bi,bo,?_,?_,bkin,
    ⟨bc.z,bc.one,bc.two⟩,fun x hx=>bfr x hx⟩
  · simpa only [hp,mr,maskMomentRequest_left,maskMomentRequest_right] using hn
  · exact bflag.trans (congrArg Bool.toNat (maskMomentRequest_structural r index edge))
  · funext store
    change b.ram (preparedPermutation.symm store)=a.ram store
    rw [bram]
    simp only [old,permuteMemory,Equiv.symm_symm,Equiv.apply_symm_apply]
  · funext store
    change b.rc (preparedPermutation.symm store)=a.rc store
    rw [brc]
    simp only [old,permuteMemory,Equiv.symm_symm,Equiv.apply_symm_apply]

end NearQuarticWires.StageLiftMasks
