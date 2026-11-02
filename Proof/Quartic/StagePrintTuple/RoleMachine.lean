import Proof.Quartic.StagePrintTuple.RoleProgram
import Proof.Quartic.StageRecovery.PacketRequest
import Proof.Gates.Cells.Prelude

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells

/-- `prop:time`, paper/paper.tex: the role packet's
binary workspace is a fixed polynomial in its first actual affine
field, the original input arity. -/
def RolePacket.widthBound (r : RolePacket) : ℕ := 64*(r.scalars 0+1)^4

/-- `lem:print` and `prop:time`, paper/paper.tex: validity bounds only the actual encoded
packet and its deterministic output scalars; it supplies no selected
row, child pool, decoded role or output length. -/
structure RoleRequest where
  packet : RolePacket
  fields_fit : ∀ v ∈ packet.values,natBitLength v+2≤packet.widthBound
  radix_pos : 0<packet.radix
  banks_fit : 2*(packet.firstCount+packet.secondCount)≤2^packet.widthBound
  radix_fit : 2*packet.radix≤2^packet.widthBound
  output_fit : ∀ v ∈ packet.outputValues,natBitLength v+2<2^packet.widthBound

/-- `lem:print`, paper/paper.tex:
the proof-only validity fields do not change the literal source codec. -/
def RoleRequest.word (r : RoleRequest) : List Bool := r.packet.word

/-- `prop:time`, paper/paper.tex: the actual first
arity codec initializes a fourth-power binary workspace. -/
def roleSizes : Sz := ⟨64,4,0,0,0,0⟩

/-- `prop:time`, paper/paper.tex: the actual role
source begins with its original arity field, so setup reads a real
polynomial workspace header rather than the exponential walk address. -/
theorem RoleRequest.context_width (r : RoleRequest) :
    r.packet.widthBound ≤ (ctxOf StageRecovery.packetCallee roleSizes r.word).Wd := by
  let tail := ((List.ofFn fun j : Fin 6=>r.packet.scalars j.succ) ++
    [r.packet.firstCount,r.packet.secondCount,r.packet.radix,r.packet.address,r.packet.atom.val]).flatMap natWord
  have hw : r.word=natWord (r.packet.scalars 0)++tail := by
    simp only [RoleRequest.word,RolePacket.word,RolePacket.values,List.ofFn_succ,
      List.cons_append,List.flatMap_cons]
    rfl
  have hl : leadOnes r.word=natBitLength (r.packet.scalars 0) := by
    rw [hw]
    exact NearCubicGates.Close.CounterMachine.PrefixProg.leadOnes_natWord _ _
  change 64*(r.packet.scalars 0+1)^4≤2^(4*leadOnes r.word)*64
  rw [hl]
  have hp : r.packet.scalars 0+1≤2^natBitLength (r.packet.scalars 0) :=
    lt_natBitLength (r.packet.scalars 0)
  have hb := Nat.pow_le_pow_left hp 4
  rw [←pow_mul] at hb
  simpa only [Nat.mul_comm] using Nat.mul_le_mul_left 64 hb

/-- `lem:print`, paper/paper.tex:
the complete role machine initializes its constants before parsing any
actual affine field or computing any occurrence index. -/
def coldRoleProgram : St VV MM := .seq initP roleProgram

/-- `prop:time`, paper/paper.tex: the complete
cold role clock includes all constant initialization instructions. -/
def RoleRequest.steps (r : RoleRequest) : ℕ := r.packet.steps+6

attribute [local irreducible] roleProgram RolePacket.values RolePacket.outputValues
  RolePacket.widthBound RolePacket.steps

/-- `lem:print` and `prop:time`, paper/paper.tex: the source-to-header program starts with
zero registers and produces exactly the original occurrence and affine
metadata from the actual packet bytes. -/
theorem coldRoleProgram_spec (C : Ctx) (r : RoleRequest)
    (hin : C.inp=r.word) (hwidth : r.packet.widthBound≤C.Wd) :
    Hs C coldRoleProgram (a0 : DS VV MM) r.steps (fun b=>b.out=r.packet.output) := by
  have hsmallW : 64≤r.packet.widthBound := by
    unfold RolePacket.widthBound
    have h := Nat.pow_le_pow_left (by omega : 1≤r.packet.scalars 0+1) 4
    norm_num at h
    omega
  have hp := Nat.pow_le_pow_right (by decide : 1≤(2:ℕ)) hwidth
  have hcap : 17<2^C.Wd := by
    have h : 17<2^64 := by decide
    exact h.trans_le (Nat.pow_le_pow_right (by decide) (hsmallW.trans hwidth))
  unfold coldRoleProgram RoleRequest.steps
  refine (Hs.seq (t2:=r.packet.steps)
    (initP_spec (C:=C) (a0 : DS VV MM) rfl rfl rfl (by omega)) ?_).mono
    (by omega) (fun _ h=>h)
  rintro a ⟨ac,_ar,_arc,ai,ao,_ak,_ako,_akc,_af⟩
  have he := roleProgram_spec C r.packet [] a ac
    (by rw [ai,hin];simp [a0,RoleRequest.word])
    (by intro v hv;exact (r.fields_fit v hv).trans hwidth)
    (by omega) r.radix_pos (r.banks_fit.trans hp) (r.radix_fit.trans hp) hcap
    (by intro v hv;exact (r.output_fit v hv).trans_le hp)
  refine he.mono le_rfl ?_
  rintro b ⟨bo,_⟩
  rw [bo,ao]
  rfl

/-- `prop:time`, paper/paper.tex: the role
subroutine's budget includes genuine binary setup, ordinary simulation
and final tape and register return. -/
noncomputable def RoleRequest.budget (r : RoleRequest) : ℕ :=
  langBudget StageRecovery.packetCallee roleSizes VV MM r.word r.steps

/-- `lem:print`, paper/paper.tex:
the genuine cold ordinary word function computes the actual complete
row-role result from its encoded scalar source packet alone. -/
noncomputable def roleWordFunction :
    WordFunction RoleRequest RoleRequest.word (fun r=>r.packet.output) RoleRequest.budget :=
  wordFunction_of_lang RoleRequest.word (fun r=>r.packet.output)
    StageRecovery.packetCallee roleSizes coldRoleProgram RoleRequest.steps
    (by
      intro r
      obtain ⟨b,n,he,hn,ho⟩ := coldRoleProgram_spec
        (ctxOf StageRecovery.packetCallee roleSizes r.word) r rfl r.context_width
      exact ⟨b,n,he,ho,hn⟩)
    (by
      intro r
      have h := r.context_width
      have h0 : 1≤r.packet.widthBound := by
        unfold RolePacket.widthBound
        have hh : 0<(r.packet.scalars 0+1)^4 := Nat.pow_pos (by omega)
        omega
      exact h0.trans h)

end NearQuarticWires.StageTuple
