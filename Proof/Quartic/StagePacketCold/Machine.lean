import Proof.Quartic.StagePacketCold.Strip
import Proof.Quartic.StagePrint.IndexedPacketTarget

set_option autoImplicit false

namespace NearQuarticWires.StagePacketCold

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Expand.PolyTab
open NearCubicGates.Close.Interfaces.Formats
open StagePrint.Downstream

/-- `lem:print` and `prop:time`, paper/paper.tex: measured finite-packet stripping gives one fixed
ordinary machine, including physical rewind of every used tape.
The prefix decomposition is correctness data, not runtime metadata. -/
noncomputable def stripWordFunction {Request : Type} (count : ℕ)
    (input : Request→List Bool) (fields : Request→List ℕ) (body : Request→List Bool)
    (hinput : ∀ request,input request=(fields request).flatMap natWord++body request)
    (hcount : ∀ request,(fields request).length=count) :
    WordFunction Request input (fun request=>frame (body request))
      (fun request=>10^8*((input request).length+1)^2) :=
  wordFunction_of_ideal (.wm (stripPrefix count)) (2 : Fin 3) (by decide)
    (fun request=>10*((input request).length+1)) (fun _ _=>0)
    (fun request=>300*((input request).length+1))
    (by intro request;nlinarith [Nat.zero_le (input request).length])
    (by
      intro request
      obtain ⟨last,hrun,hout⟩:=stripPrefix_run (fields request) (body request)
      rw [hcount request,←hinput request] at hrun
      exact ⟨rfl,last,hrun,hout⟩)

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual cold exact-CERT adapter strips six binary
indexed fields and emits its unchanged original signed Formula frame. -/
noncomputable def exactPacketProjection : ExactPacketProjection :=
  stripWordFunction 6 StagePrint.PacketInterface.ExactProjectionRequest.word StagePacket.projectionHeader
    (fun request=>formulaWord request.formula) StagePacket.projection_word (fun _=>rfl)

/-- `lem:print`, `lem:residue` and `prop:time`, paper/paper.tex: the actual cold modular
adapter removes only the binary encoded index and preserves the
unchanged finite-family compiler request for every allowed modulus. -/
noncomputable def modularPacketProjection : ModularPacketProjection :=
  stripWordFunction 1 IndexedFamilyPacket.word (fun request=>[request.index])
    (fun request=>request.request.word)
    (by intro request;simp only [IndexedFamilyPacket.word,List.flatMap_cons,List.flatMap_nil,List.append_nil])
    (fun _=>rfl)

end NearQuarticWires.StagePacketCold
