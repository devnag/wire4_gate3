import Proof.Quartic.StagePrintTuple.SupportIndex
import Proof.Quartic.StagePrintTuple.HistoryData

set_option autoImplicit false

namespace NearQuarticWires.StageTuple

open NearCubicWires.RepairRepresentation (natWord)

/-- `lem:print`, paper/paper.tex: the actual
selector sees the literal natural codecs of the finite formula atoms,
with the same physically computed reverse position. -/
def finiteSupportRequest {V : ℕ} (order : List (Fin V))
    (j : Fin order.length) : SupportIndexRequest where
  support := order.map Fin.val
  index := ⟨j.val,by rw [List.length_map];exact j.isLt⟩

/-- `lem:print`, paper/paper.tex: selecting
from the serialized finite support produces exactly the original
atom codec, without changing its occurrence or star-role index. -/
theorem finiteSupportRequest_output {V : ℕ} (order : List (Fin V))
    (j : Fin order.length) :
    (finiteSupportRequest order j).output=natWord order[j.val].val := by
  simp [finiteSupportRequest,SupportIndexRequest.output]

/-- `lem:print`, paper/paper.tex: the real
decremented reverse counter identifies the next atom before the
already processed suffix, rather than enumerating a fresh tuple order. -/
def reverseSupportIndex {ι : Type} (order : List ι) (done : ℕ)
    (hd : done<order.length) : Fin order.length :=
  ⟨order.length-(done+1),by omega⟩

/-- `lem:print`, paper/paper.tex: the next
selected source atom is prepended to exactly the current suffix. -/
theorem reverseSupportIndex_suffix {ι : Type} (order : List ι) (done : ℕ)
    (hd : done<order.length) :
    processedSupport order (done+1)=
      order[(reverseSupportIndex order done hd).val]::processedSupport order done :=
  processedSupport_succ order done hd

end NearQuarticWires.StageTuple
