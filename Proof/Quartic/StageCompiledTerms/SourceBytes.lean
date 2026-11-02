import Proof.Quartic.StageLift.SourceMachine
import Proof.Quartic.StageLiftSourceCost.Walks

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCompiledTerms

open NearCubicWires NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces (listWord)
open NearCubicWires.RepairRepresentation (natWord)
open StageLift

/-- Step 3 and `cor:conditional`, paper/paper.tex: every literal Gamma prefix cursor is
bounded by the real retained Gamma word, including the final cursor. -/
theorem gamma_cursor_length_le {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) (index : ℕ) :
    gammaByteCursor r index≤
      (listWord NearCubicGates.Close.Interfaces.intWord (Greedy.gammaTable r.child)).length := by
  have hsplit:=List.take_append_drop index (Greedy.gammaTable r.child)
  have hlen:=congrArg (fun entries=>
    (entries.flatMap NearCubicGates.Close.Interfaces.intWord).length) hsplit
  rw [List.flatMap_append,List.length_append] at hlen
  simp only [gammaByteCursor,listWord,List.length_append,actualGamma_length]
  omega

/-- `prop:time`, paper/paper.tex: the checked
source invariant permits a mathematical byte-length comparison at any
real retained Gamma cursor. This changes no source or formula bytes. -/
theorem source_state_at_cursor {B1 B2 : ℕ} {C : Ctx} {r : Greedy.PrintRequest B1 B2}
    {a : DS VV MM} (ha : WalkSourceState C r 0 a) (index : ℕ) :
    WalkSourceState C r index {a with rc:=Function.update a.rc gammaStore (gammaByteCursor r index)} := by
  let b : DS VV MM:={a with rc:=Function.update a.rc gammaStore (gammaByteCursor r index)}
  have hview : sourceEntryView r b=sourceEntryView r a := by
    simp only [sourceEntryView,b,Function.update_idem]
  have hram : a.ram gammaStore=
      (listWord NearCubicGates.Close.Interfaces.intWord (Greedy.gammaTable r.child)).map Bool.toNat :=
    ha.sources.gammaBits
  refine ⟨?_,?_,?_,?_,ha.inputEmpty⟩
  · change CarrierStartData r (sourceEntryView r b)
    rw [hview]
    exact ha.sources
  · simp [b]
  · exact ⟨ha.constants.z,ha.constants.one,ha.constants.two⟩
  · have hv:=ha.validExceptCounter
    refine ⟨hv.env_lt,hv.ip_le,hv.ram_lt,?_,hv.kin_le,hv.kout_le,hv.kc_le⟩
    intro store
    by_cases he : store=gammaStore
    · subst store
      simpa only [DS.set,b,Function.update_self,hram,List.length_map] using gamma_cursor_length_le r index
    · simpa only [DS.set,b,Function.update_of_ne he] using hv.rc_le store

/-- `lem:print` and `prop:time`, paper/paper.tex: the literal unreduced packet's byte
length is bounded by its actual complete physical writer clock.
The source invariant exists by the proved cold original-input startup. -/
theorem source_packet_length_le {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2)
    (index : Fin (r.child.cellCall.seed.N^8)) :
    (sourceWalkPacket r index).word.length≤
      walkPacketCost r (printSourceContext B1 B2 (Greedy.printInput r)).Lk
        (printSourceContext B1 B2 (Greedy.printInput r)).Bk := by
  obtain ⟨a,ta,hea,hta,_haout,hasource,_hainput,hakin,hac,hav⟩:=coldCarrierInitialize_spec r
  have ha:=WalkSourceState.of_start hasource hac hav hakin
  let b : DS VV MM:={a with rc:=Function.update a.rc gammaStore (gammaByteCursor r index.val)}
  have hb:=source_state_at_cursor ha index.val
  have hc:=hb.setCounter index.val
  obtain ⟨z,n,he,hn,hout,_hstate,_hi,_hip⟩:=emitWalkPacket_spec r index
    (b.set printWalkIndex index.val) hc rfl
  have hlen:=he.out_len
  rw [hout,List.length_append] at hlen
  omega

/-- `prop:time`, paper/paper.tex: every actual
unreduced source packet has one guarded-tuple enumeration factor and
a fixed polynomial scalar multiplier, independent of raw index length. -/
theorem source_packet_length_scale {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2)
    (index : Fin (r.child.cellCall.seed.N^8)) :
    (sourceWalkPacket r index).word.length+1≤
      7000000000000*(Builder.allGates r.child.call).length^r.child.selected.1.Xmax*
        (StageLiftSourceCost.sourceScale r)^30 := by
  let S:=StageLiftSourceCost.sourceScale r
  let M:=(Builder.allGates r.child.call).length^r.child.selected.1.Xmax
  have hlen:=source_packet_length_le r index
  have hp:=StageLiftSourceCost.walk_payload_scale r
  have hs : 1≤S := by have h:=(StageLiftSourceCost.sourceScale_small r).1;omega
  have hm : 1≤M:=StageLiftSourceCost.original_tuple_pos r
  have hE:=Nat.pow_le_pow_left (StageLiftSourceCost.sourceScale_small r).2.1 2
  have h2 : S^2≤S^30:=Nat.pow_le_pow_right hs (by decide)
  have h0 : 1≤S^30:=Nat.pow_pos hs
  have hMS:=Nat.mul_le_mul_right (S^30) hm
  dsimp only at hp
  unfold walkPacketCost at hlen
  change walkPayloadCost r _ _≤2000000000000*M*S^30 at hp
  change (sourceEnvelope r+1)^2≤S^2 at hE
  change _≤7000000000000*M*S^30
  nlinarith only [hlen,hp,hE,h2,h0,hMS]

end NearQuarticWires.StageCompiledTerms
