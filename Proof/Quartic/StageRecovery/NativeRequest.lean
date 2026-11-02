import Proof.Quartic.StageRecovery.FramedNativeTable
import Proof.Quartic.StageRecovery.PacketPrefixCost
import Proof.Quartic.StageRecovery.TablePacket

set_option autoImplicit false

namespace NearQuarticWires.StageRecovery

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces

/-- `lem:print` and `lem:residue`, paper/paper.tex: the actual complete reduced-coefficient native table and
its original-column target count, with no supplied table entries. -/
structure NativeRequest where
  table : StagePrint.TableRequest
  modulus : ℕ
  modulus_pos : 0 < modulus
  nonnegative : ∀ cut ∈ table.matrix.cuts, 0 ≤ cut.coefficient
  targetCount : ℕ
  targetCount_le : targetCount ≤ table.count

/-- `lem:print`, paper/paper.tex: the native wrapper
receives one literal fixed eleven-field load record. Its only nonempty
fields are the modulus codec, actual framed native input and target-count codec. -/
def NativeRequest.word (r : NativeRequest) : List Bool :=
  Top.loadRec (natWord r.modulus) (frame r.table.word) (natWord r.targetCount)
    [] [] [] [] [] [] [] []

/-- `prop:time`, paper/paper.tex: every actual
native-wrapper field, including the full native input, is charged by
the unchanged fixed-loader clock. -/
def NativeRequest.loadCost (r : NativeRequest) : ℕ :=
  Top.loadCost (natWord r.modulus) (frame r.table.word) (natWord r.targetCount)
    [] [] [] [] [] [] [] []

/-- `prop:time`, paper/paper.tex: the fixed-loader
capacity includes the complete literal outer record and all actual
field-copy work; it is a proof-space bound rather than supplied data. -/
def NativeRequest.loadCapacity (r : NativeRequest) : ℕ :=
  2 * r.word.length + 1 + Top.loadChainCost (natWord r.modulus)
    (frame r.table.word) (natWord r.targetCount) [] [] [] [] [] [] [] []

/-- `lem:print` and `lem:residue`, paper/paper.tex: the existing native nonnegative-table semantics supply
the already checked bounded packet specification. -/
def NativeRequest.packet (r : NativeRequest) : PacketRequest :=
  tablePacket r.table r.modulus r.modulus_pos r.nonnegative

/-- `lem:print`, paper/paper.tex: the actual target
count is bounded by the complete native row-major table, including odd
free-dimension padding handled by the source's prefix-orientation proof. -/
def NativeRequest.prefix (r : NativeRequest) : PacketPrefixRequest where
  native := r.packet
  count := r.targetCount
  count_le := by
    change r.targetCount ≤ (tableNaturals r.table).length
    rw [tableNaturals_length]
    exact r.targetCount_le

/-- `lem:print`, paper/paper.tex: the recovered
output consists of the canonical centered original-column prefix of
the complete actual native table in its existing row-major order. -/
def NativeRequest.output (r : NativeRequest) : List Bool := r.prefix.output

/-- `lem:print`, paper/paper.tex: the concrete
recovery handoff is precisely three actual header fields followed by
the native printer's unchanged complete record packet. -/
theorem NativeRequest.prefix_word (r : NativeRequest) :
    r.prefix.word = natWord r.packet.hint ++ natWord r.modulus ++ natWord r.targetCount ++ r.table.output := by
  have hstream : packetStream r.packet.width r.packet.values = r.table.output :=
    tablePacket_stream r.table r.modulus r.modulus_pos r.nonnegative
  change natWord r.packet.hint ++ natWord r.modulus ++ natWord r.targetCount ++
    packetStream r.packet.width r.packet.values = _
  rw [hstream]

/-- `lem:print`, paper/paper.tex: fixed outer
extraction produces thirteen actual loaded streams: original frame,
raw input and the eleven source fields. -/
def NativeRequest.fields (r : NativeRequest) : Fin 13 → List Bool :=
  ![frame r.word, r.word, natWord r.modulus, frame r.table.word, natWord r.targetCount,
    [], [], [], [], [], [], [], []]

/-- `lem:print`, paper/paper.tex: the exact
physical state after the cold fixed outer load preserves the actual
native framed input on stream three and both actual codecs separately. -/
def NativeRequest.loaded (r : NativeRequest) :
    NearCubicWires.WireExponent3_5.FinalPass.Tm.WState 13 10 :=
  ⟨fun _ => 0,
    Fin.addCases (m := 13) (n := 1) (motive := fun _ => List Bool) r.fields
      (fun _ : Fin 1 => List.replicate r.loadCapacity false),
    fun _ => 0, false⟩

end NearQuarticWires.StageRecovery
