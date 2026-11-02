import Proof.Quartic.StagePrint.RawCallGate
import Proof.Quartic.StagePrint.RawSecondCallGate
import Proof.Quartic.StagePrint.RawInitialization

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint.RawBits
open NearCubicGates.Close.Dispatch
open NearCubicGates.Close.Interfaces
open NearCubicWires
open NearCubicWires.RepairRepresentation (natWord)

/-- `lem:print`, paper/paper.tex: selection between the two original occurrence banks does not alter any gate. -/
def originalCircuit (second : Bool) (c : Call) : NCircuit c.n :=
  if second then c.second else c.first

/-- `lem:print`, paper/paper.tex: the selected call and occurrence are serialized, not supplied as a child list. -/
structure IndexedCallGateRequest (second : Bool) where
  call : Call
  index : Fin (originalCircuit second call).gates.length
  gate_bits : NearCubicGates.Close.Tabulator.GateBits (Call.B0 call.n)
    (originalCircuit second call).gates[index.val]
  suffix : List Bool

/-- `lem:print`, paper/paper.tex: the physical occurrence selector precedes the unchanged call word. -/
def IndexedCallGateRequest.source {second : Bool} (r : IndexedCallGateRequest second) : List Bool :=
  natWord r.index.val++callWord r.call++r.suffix

/-- `lem:print`, paper/paper.tex: the original sharp decomposition request for that occurrence. -/
def IndexedCallGateRequest.child {second : Bool} (r : IndexedCallGateRequest second) : OriginalChildRequest :=
  originalChildRequest (Call.B0 r.call.n) (originalCircuit second r.call).gates[r.index.val] r.gate_bits

/-- `lem:print`, paper/paper.tex: bank selection is a fixed branch of the physical program. -/
def selectCallBank (second : Bool) : St VV := if second then secondCallGate else firstCallGate

/-- `prop:time`, paper/paper.tex: the complete scan of either original bank is included. -/
def IndexedCallGateRequest.selectSteps {second : Bool} (C : Ctx) (r : IndexedCallGateRequest second) : ℕ :=
  circCost C.cw.length+100*C.cw.length+300+5*Nat.clog 2 (r.call.n+1)+
    30*natBitLength (originalCircuit second r.call).gates.length+
    selectOriginalCost C r.index.val r.child

/-- `lem:print`, paper/paper.tex: a selected occurrence is read from an actual call prefix. -/
theorem selectCallBank_run (C : Ctx) (second : Bool) (r : IndexedCallGateRequest second)
    (a : DS VV) (hc : Cst a) (hcw : C.cw.drop a.cp=callWord r.call++r.suffix)
    (hj : a.env selectedGate=r.index.val) (hspace : 5*(C.cw.length+2)^2≤C.Wd) :
    Hs C (selectCallBank second) a (r.selectSteps C)
      (fun b=>b.out=a.out++r.child.word ∧ b.wq=a.wq ∧ Cst b) := by
  cases second
  · exact (firstCallGate_run C r.call r.index r.gate_bits r.suffix a hc hcw hj hspace).mono
      (by simp only [IndexedCallGateRequest.selectSteps,IndexedCallGateRequest.child,originalCircuit,Bool.false_eq_true,ite_false,ite_true];omega) (fun _ h=>h)
  · exact (secondCallGate_run C r.call r.index r.gate_bits r.suffix a hc hcw hj hspace).mono
      (by simp only [IndexedCallGateRequest.selectSteps,IndexedCallGateRequest.child,originalCircuit,Bool.false_eq_true,ite_false,ite_true];omega) (fun _ h=>h)

/-- `lem:print`, paper/paper.tex: constants and the occurrence index are physically read from the cold source. -/
def indexedCallGate (second : Bool) : St VV :=
  .seq initializeConstants (.seq readNat
    (.seq (.op (.copy selectedGate t3)) (selectCallBank second)))

/-- `prop:time`, paper/paper.tex: the cold occurrence selector has a full source clock. -/
def IndexedCallGateRequest.steps {second : Bool} (C : Ctx) (r : IndexedCallGateRequest second) : ℕ :=
  30*natBitLength r.index.val+r.selectSteps C+50

/-- `lem:print`, paper/paper.tex: the complete actual call word yields the exact original-child setup without preinitialized registers. -/
theorem indexedCallGate_run (C : Ctx) (second : Bool) (r : IndexedCallGateRequest second)
    (hcw : C.cw=r.source) (hspace : 5*(C.cw.length+2)^2≤C.Wd) :
    Hs C (indexedCallGate second) (a0 (V:=VV)) (r.steps C)
      (fun b=>b.out=r.child.word) := by
  have hW : C.cw.length+3≤C.Wd := by nlinarith
  have hbit : natBitLength r.index.val≤C.cw.length := by
    have h:=natBitLength_le_len r.index.val
    rw [hcw,IndexedCallGateRequest.source,List.length_append,List.length_append]
    omega
  have hidx : r.index.val<2^C.Wd := lt_of_lt_of_le (lt_natBitLength _)
    (Nat.pow_le_pow_right (by decide) (hbit.trans (by omega)))
  have hlen : C.cw.length+2<2^C.Wd := lt_of_le_of_lt (by omega) Nat.lt_two_pow_self
  unfold indexedCallGate
  refine Hx.hs (Hs.then (initialize_run C (by omega)) (fun a ⟨ac,ap,_,ao,_⟩ n1 hn1=>?_))
  have ad : C.cw.drop a.cp=natWord r.index.val++(callWord r.call++r.suffix) := by
    rw [ap,List.drop_zero,hcw,IndexedCallGateRequest.source,List.append_assoc]
  refine Hs.then (readNat_spec a ac r.index.val _ ad (by omega) hlen)
    (fun b ⟨bv,_,bp,_,bo,bc,_⟩ n2 hn2=>?_)
  refine Hs.then (hs_copy C selectedGate t3 b (by decide)) (fun e he n3 hn3=>?_)
  subst he
  let e:=b.set selectedGate (b.env t3)
  have ef : Fr b e [selectedGate] := Fr.set _ _ (by simp)
  have ec : Cst e:=Cst.of_fr bc ef (by decide)
    (by rw [ef vPOS (by decide)];exact bc.pos)
  have ed : C.cw.drop e.cp=callWord r.call++r.suffix := by
    change C.cw.drop b.cp=_
    rw [bp,←List.drop_drop,ad,List.drop_left]
  refine Hs.last (selectCallBank_run C second r e ec ed (by simp [e,bv]) hspace)
    (fun f ⟨fo,_⟩ n4 hn4=>?_)
  refine ⟨?_,?_⟩
  · simpa only [e,DS.set_out,bo,ao,List.nil_append] using fo
  · unfold IndexedCallGateRequest.steps
    omega

end NearQuarticWires.StagePrint.RawBits
