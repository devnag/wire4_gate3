import Proof.Quartic.StageNativeRowCount.ParseHeader
import Proof.Quartic.StageNativeRowCount.Arithmetic
import Proof.Quartic.StageNativeRowCount.Widths
import Proof.Quartic.StageRecovery.NaturalPrint
import Proof.Gates.Cells.Prelude

set_option autoImplicit false

namespace NearQuarticWires.StageNativeRowCount

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells

/-- `lem:print`, paper/paper.tex: retain actual
framed header bytes, rewind them once, read n/r/b and compute the count. -/
def bodyProgram : St VV MM :=
  .seq (StageLift.readFrame headerStore)
    (.seq (.op (.rwM headerStore))
      (.seq (parseHeader (fun x=>.rdM headerStore x))
        (.seq countProgram (StageRecovery.emitVariable countReg))))

def Request.bodyClock (r : Request) : ℕ :=
  9*r.payload.length+
    parseHeaderCost r.header.call.n r.sourceWidth r.nativeWidth
      r.header.parameters.r r.header.parameters.b+
    40*natBitLength r.rowFieldCount+100

/-- `imp:pullback`, `lem:print` and `prop:time`, paper/paper.tex: actual finite header bits,
not decoded metadata or a dimension oracle, produce the exact count. -/
theorem bodyProgram_spec (C : Ctx) (r : Request) (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip=r.word) (hram : a.ram headerStore=[])
    (hrc : a.rc headerStore=0) (hwidth : 100*(r.header.call.n+1)^2≤C.Wd) :
    Hs C bodyProgram a r.bodyClock (fun d=>d.out=a.out++natWord r.rowFieldCount) := by
  let n:=r.header.call.n
  have hT : 1≤(n+1)^2 := Nat.pow_pos (Nat.succ_pos _)
  have hW : ∀v∈r.firstFive,natBitLength v+2≤C.Wd := by
    intro v hv
    have hh:=r.firstFive_bound v hv
    have hb:=bitLength_le v
    change v≤16*(n+1)^2 at hh
    change 100*(n+1)^2≤C.Wd at hwidth
    omega
  have hnC : 4*n+6<2^C.Wd := by
    have hh:=Nat.lt_two_pow_self (n:=C.Wd)
    change 100*(n+1)^2≤C.Wd at hwidth
    have hnn : 4*n+6≤100*(n+1)^2 := by nlinarith
    omega
  unfold bodyProgram
  refine Hx.hs (Hs.then (StageLift.readFrame_spec C headerStore r.payload [] a hc
    (by simpa only [Request.word,List.append_nil] using hin) (by rw [hram,hrc];rfl)) ?_)
  rintro b ⟨_,br,bcursor,_,bsh,bc,_⟩ k0 hk0
  have bram : b.ram headerStore=r.payload.map Bool.toNat := by rw [br,hram,List.nil_append]
  have bout : b.out=a.out := congrArg Prod.fst bsh
  have bcursor' : b.rc headerStore=r.payload.length := by rw [bcursor,hrc,Nat.zero_add]
  refine Hs.then (Hs.op (OpEx.rwM headerStore b) rfl) ?_
  rintro c rfl k1 hk1
  let S:=StageLift.memorySource C headerStore r.payload
  have cc : Cst (b.rew headerStore) := ⟨bc.z,bc.one,bc.two⟩
  have cok : S.ok (b.rew headerStore) := bram
  have ci : S.word.drop (S.pos (b.rew headerStore)) = r.firstFive.flatMap natWord ++
      [r.header.parameters.s,StagePullback.translationNumber
        (Builder.star r.header.call r.header.prepared)
        (Builder.translation r.header.call r.header.prepared r.header.witness)].flatMap natWord := by
    change r.payload.drop 0=_
    rw [List.drop_zero,r.payload_split]
  refine Hs.then (parseHeader_spec S (b.rew headerStore) cc cok
    r.header.call.n r.sourceWidth r.nativeWidth r.header.parameters.r r.header.parameters.b
    _ ci hW) ?_
  rintro d ⟨dn,dr,db,drest,dc⟩ k2 hk2
  have dout : d.out=a.out := by
    have hh:=congrArg (fun t=>t.2.1) drest
    change d.out=b.out at hh
    exact hh.trans bout
  refine Hs.then (countProgram_spec C d dc _ _ _ dn dr db r.geometry_bounds.1
    (by change 4*n+4<2^C.Wd;omega)) ?_
  rintro e ⟨ecount,esh,ec⟩ k3 hk3
  have ecount' : e.env countReg=r.rowFieldCount := ecount.trans r.count_eq.symm
  have eout : e.out=a.out := (congrArg (fun t=>t.2.1) esh).trans dout
  have hbcount : natBitLength r.rowFieldCount+2<2^C.Wd := by
    have hh:=bitLength_le r.rowFieldCount
    have hc:=r.count_bound
    change r.rowFieldCount≤4*n+3 at hc
    omega
  refine Hs.last (StageRecovery.emitVariable_spec C e ec countReg (by decide)
    (by change 100*(n+1)^2≤C.Wd at hwidth;omega) (by rw [ecount'];exact hbcount)) ?_
  rintro f ⟨fo,_,_,_⟩ k4 hk4
  refine ⟨?_,?_⟩
  · rw [fo,ecount',eout]
  · rw [ecount'] at hk4
    rw [bcursor'] at hk1
    unfold Request.bodyClock
    omega

def unframedProgram : St VV MM := .seq initP bodyProgram

def Request.unframedClock (r : Request) : ℕ := r.bodyClock+6

/-- `lem:print`, paper/paper.tex: the scalar
producer starts with actual zero registers/stores and its existing frame. -/
theorem unframedProgram_spec (C : Ctx) (r : Request) (hin : C.inp=r.word)
    (hwidth : 100*(r.header.call.n+1)^2≤C.Wd) :
    Hs C unframedProgram (a0 : DS VV MM) r.unframedClock (fun d=>d.out=natWord r.rowFieldCount) := by
  have hW : 2≤C.Wd := by
    have hT : 1≤(r.header.call.n+1)^2 := Nat.pow_pos (Nat.succ_pos _)
    omega
  have hroom : 2<2^C.Wd := by
    have hh : 4≤2^C.Wd := Nat.pow_le_pow_right (n:=2) (by decide) hW
    omega
  unfold unframedProgram Request.unframedClock
  refine (Hs.seq (t1:=5) (t2:=r.bodyClock)
    (initP_spec (C:=C) (a0 : DS VV MM) rfl rfl rfl hroom) ?_).mono (by omega) (fun _ h=>h)
  rintro a ⟨hc,hr,hrc,hi,ho,_,_,_,_⟩
  refine (bodyProgram_spec C r a hc (by
    rw [hi]
    change C.inp.drop 0=r.word
    rw [List.drop_zero,hin])
    (by rw [hr];rfl) (by rw [hrc];rfl) hwidth).mono le_rfl ?_
  rintro d hd
  simpa only [ho,a0,List.nil_append] using hd

/-- `lem:print`, paper/paper.tex: output marking
is an actual syntax transformation with a paid final delimiter. -/
def program : St VV MM := StageRecovery.OutputFrame.framedProgram unframedProgram

def Request.sourceClock (r : Request) : ℕ := 3*r.unframedClock+2

theorem program_spec (C : Ctx) (r : Request) (hin : C.inp=r.word)
    (hwidth : 100*(r.header.call.n+1)^2≤C.Wd) :
    Hs C program (a0 : DS VV MM) r.sourceClock (fun d=>d.out=r.output) := by
  obtain ⟨b,k,he,hk,ho⟩:=unframedProgram_spec C r hin hwidth
  have hh:=StageRecovery.OutputFrame.framedProgram_spec he
  refine ⟨StageRecovery.OutputFrame.framedState b,3*k+2,hh,by unfold Request.sourceClock;omega,?_⟩
  change frame b.out=r.output
  rw [ho]
  rfl

end NearQuarticWires.StageNativeRowCount
