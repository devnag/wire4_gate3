import Proof.Quartic.StageLift.PreparedOutput
import Proof.Quartic.StageLift.OutputPrefix
import Proof.Quartic.StageRecovery.NaturalPrint

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint.EntryFormat

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells

/-- `lem:print`, paper/paper.tex: the actual
walk ordinal is retained outside all codec and memory-copy scratch. -/
def indexVar : Fin VV := 70

/-- `lem:print`, paper/paper.tex: the retained
three source count codecs are followed by the actual walk codec. -/
def rawContextProgram : St VV MM :=
  .seq StageLift.emitPreparedWord (StageRecovery.emitVariable indexVar)

/-- `lem:print`, paper/paper.tex: copying the
small source context and writing the binary ordinal preserve all
following source and the complete retained Terms field. -/
theorem rawContextProgram_run (C : Ctx) (bits : List Bool) (index : ℕ)
    (a : DS VV MM) (hc : Cst a)
    (hbits : a.ram StageLift.preparedStore=bits.map Bool.toNat)
    (hlen : a.env StageLift.preparedLength=bits.length)
    (hi : a.env indexVar=index) (hfit : bits.length<2^C.Wd)
    (hW : 2≤C.Wd) (hindex : natBitLength index+2<2^C.Wd) :
    Hs C rawContextProgram a
      (a.rc StageLift.preparedStore+8*bits.length+40*natBitLength index+49) (fun b =>
      b.out=a.out++(bits++natWord index) ∧ b.ip=a.ip ∧ b.ram=a.ram ∧
      b.rc=Function.update a.rc StageLift.preparedStore bits.length ∧
      (b.kin,b.kout,b.kc)=(a.kin,a.kout,a.kc) ∧ Cst b ∧
      Fr a b [c0,t0,t3,t5,t6,t7,t8,t9]) := by
  unfold rawContextProgram
  refine (Hs.seq (t2:=40*natBitLength index+42)
    (StageLift.emitPreparedWord_spec C bits a hc hbits hlen hfit)
    fun d ⟨dout,di,dr,drc,dk,dc,dfr⟩ => ?_).mono (by omega) (fun _ h=>h)
  have dix : d.env indexVar=index := by rw [dfr _ (by decide),hi]
  have er:=StageRecovery.emitVariable_spec C d dc indexVar (by decide) hW
    (by rwa [dix])
  rw [dix] at er
  refine er.mono le_rfl ?_
  rintro b ⟨bout,brest,bc,bfr⟩
  simp only [Prod.mk.injEq] at brest
  rcases brest with ⟨bi,br,brc,bkin,bkout,bkc⟩
  refine ⟨?_,bi.trans di,br.trans dr,brc.trans drc,?_,bc,?_⟩
  · rw [bout,dout,List.append_assoc]
  · exact (Prod.ext bkin (Prod.ext bkout bkc)).trans dk
  · exact (dfr.weaken (by simp)).trans (bfr.weaken (by simp))

/-- `lem:print`, paper/paper.tex: the third
actual Tuple source field is framed without rewriting any preceding
output field or inferring the callee's output length. -/
def contextFieldProgram : St VV MM :=
  StageRecovery.OutputFrame.framedProgram rawContextProgram

/-- `lem:print`, paper/paper.tex: the physical
context-field emitter appends exactly one frame of original counts and
the original low-first walk ordinal, with its complete marker clock. -/
theorem contextFieldProgram_run (C : Ctx) (bits : List Bool) (index : ℕ)
    (a : DS VV MM) (hc : Cst a)
    (hbits : a.ram StageLift.preparedStore=bits.map Bool.toNat)
    (hlen : a.env StageLift.preparedLength=bits.length)
    (hi : a.env indexVar=index) (hfit : bits.length<2^C.Wd)
    (hW : 2≤C.Wd) (hindex : natBitLength index+2<2^C.Wd) :
    Hs C contextFieldProgram a
      (3*(a.rc StageLift.preparedStore+8*bits.length+40*natBitLength index+49)+2) (fun b =>
      b.out=a.out++frame (bits++natWord index) ∧ b.ip=a.ip ∧ b.ram=a.ram ∧
      b.rc=Function.update a.rc StageLift.preparedStore bits.length ∧
      (b.kin,b.kout,b.kc)=(a.kin,a.kout,a.kc) ∧ Cst b ∧
      Fr a b [c0,t0,t3,t5,t6,t7,t8,t9]) := by
  obtain ⟨b,n,he,hn,bo,bi,br,brc,bk,bc,bfr⟩ :=
    rawContextProgram_run C bits index {a with out:=[]} ⟨hc.z,hc.one,hc.two⟩ hbits hlen hi hfit hW hindex
  have hf:=StageLift.framedProgram_afterPrefix he rfl a.out
  have ha : { {a with out:=[]} with out:=a.out}=a := by cases a;rfl
  rw [ha] at hf
  change n≤a.rc StageLift.preparedStore+8*bits.length+40*natBitLength index+49 at hn
  refine ⟨{b with out:=a.out++frame b.out},3*n+2,hf,by omega,?_,bi,br,brc,bk,⟨bc.z,bc.one,bc.two⟩,bfr⟩
  simp only [bo,List.nil_append]

end NearQuarticWires.StagePrint.EntryFormat
