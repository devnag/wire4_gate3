import Proof.Quartic.StageEqualityRows.Ready

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageEqualityRows

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Recovery.HTParts
open StagePrint

def metadataSource (i : Fin 3) : Fin 24 := ![14,15,5] i

def metadataRegisters (i : Fin 3) : Fin 8 ↪ Fin 24 where
  toFun:=![metadataSource i,7,8,9,10,11,12,13]
  inj':=by fin_cases i <;> decide

def writeMetadata (i : Fin 3) : WM 15 24 := writeNatM 15 (metadataRegisters i)

/-- `lem:print`, paper/paper.tex: each measured
width or equality census is serialized using the actual binary natural
writer, with no unary decoding of signed coefficients. -/
theorem writeMetadata_run (cap : ℕ) (i : Fin 3) (a : WState 15 24) (value : ℕ)
    (hv : a.val (metadataSource i)=value)
    (hz : ∀ j : Fin 24,j.val∈[7,8,9,10,11,12]→a.val j=0)
    (ho : a.sh 15=(a.st 15).length)
    (hcap : value+a.val 13+6*natBitLength value+6≤cap) :
    WExec cap (writeMetadata i) a (appendO a 15 13 (marks (natWord value)))
      ((natBitLength value+10)*(100*value+200)) := by
  have e:=writeNatM_spec cap (15 : Fin 16) (metadataRegisters i) a
    (hz 7 (by decide)) (hz 8 (by decide)) (hz 9 (by decide))
    (hz 10 (by decide)) (hz 11 (by decide)) (hz 12 (by decide)) ho
    (by simpa [metadataRegisters,hv] using hcap)
  simpa [writeMetadata,metadataRegisters,hv] using e

theorem bitLength_le (n : ℕ) : natBitLength n≤n+1 := by
  unfold natBitLength
  have h:=Nat.log_le_self 2 n
  omega

def header1 (r : NativeStreamRequest) : WState 15 24 :=
  appendO (copyReady r) 15 13 (marks (natWord (width r)))
def header2 (r : NativeStreamRequest) : WState 15 24 :=
  appendO (header1 r) 15 13 (marks (natWord r.fieldWidth))
def header3 (r : NativeStreamRequest) : WState 15 24 :=
  appendO (header2 r) 15 13 (marks (natWord r.cuts.length))

def headerProgram : WM 15 24 :=
  .seq (writeMetadata 0) (.seq (writeMetadata 1) (writeMetadata 2))

def naturalCost (n : ℕ) : ℕ := (natBitLength n+10)*(100*n+200)

/-- `lem:print`, paper/paper.tex: the three
literal original request fields are emitted in dimension, field-width,
equality-count order, retaining the actual original row bytes. -/
theorem headerProgram_run (r : NativeStreamRequest) :
    WExec (capacity r) headerProgram (copyReady r) (header3 r)
      (naturalCost (width r)+naturalCost r.fieldWidth+naturalCost r.cuts.length+2) := by
  have hw:=bitLength_le (width r)
  have hp:=bitLength_le r.fieldWidth
  have hg:=bitLength_le r.cuts.length
  have e1:=writeMetadata_run (capacity r) 0 (copyReady r) (width r)
    (by simp [copyReady,metadataSource,counted_values])
    (by intro j hj;fin_cases j <;> simp_all [copyReady,counted_values])
    (by simp [copyReady,counted,adv,strideState,afterFields,afterWidth,loaded,lens])
    (by simp [copyReady,counted_values];unfold capacity;omega)
  have e2:=writeMetadata_run (capacity r) 1 (header1 r) r.fieldWidth
    (by simp [header1,copyReady,metadataSource,appendO,counted_values])
    (by intro j hj;fin_cases j <;> simp_all [header1,copyReady,appendO,counted_values])
    (by simp [header1,appendO,copyReady,counted,adv,strideState,afterFields,afterWidth,loaded,lens])
    (by simp [header1,appendO,copyReady,counted_values,marks_length,
      NearCubicGates.Close.CounterAsm.natWord_len];unfold capacity;omega)
  have e3:=writeMetadata_run (capacity r) 2 (header2 r) r.cuts.length
    (by simp [header2,header1,copyReady,metadataSource,appendO,counted_values])
    (by intro j hj;fin_cases j <;> simp_all [header2,header1,copyReady,appendO,counted_values])
    (by simp [header2,header1,appendO,copyReady,counted,adv,strideState,afterFields,afterWidth,loaded,lens])
    (by simp [header2,header1,appendO,copyReady,counted_values,marks_length,
      NearCubicGates.Close.CounterAsm.natWord_len];unfold capacity;omega)
  exact (e1.seq (e2.seq e3)).mono (by unfold naturalCost;omega)

end NearQuarticWires.StageEqualityRows
