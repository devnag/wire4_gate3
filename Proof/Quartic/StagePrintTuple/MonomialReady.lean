import Proof.Quartic.StagePrintTuple.MonomialFormat
import Proof.Quartic.StagePrintTuple.RegisterBounds

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close.Interfaces

/-- `lem:print`, paper/paper.tex: the actual
monomial formatter resets both newly written cache cursors using their
own physical emitted-byte counters before either cache is consumed. -/
def monomialReadyProgram : WM 2 11 :=
  .seq monomialFormatProgram (.seq (WM.rewind 1 8) (WM.rewind 2 9))

/-- `prop:time`, paper/paper.tex: one monomial
includes both real cache rewinds in its source-local clock. -/
def monomialReadyCost (L : ℕ) (support : List ℕ) (coefficient : ℤ) : ℕ :=
  monomialFormatCost L support coefficient+
    5*(frame (listWord natWord support)).length+
    5*(frame (natWord L++intWord coefficient)).length+4

/-- `lem:print` and `prop:time`, paper/paper.tex: both actual cache words and their reset heads are
established by the genuine monomial formatter and byte-counter rewinds. -/
theorem monomialReadyProgram_spec (cap L : ℕ) (support : List ℕ) (coefficient : ℤ)
    (pre rest : List Bool) (σ : WState 2 11)
    (hsource : σ.st 0=pre++listWord natWord support++intWord coefficient++rest)
    (hhead : σ.sh 0=pre.length) (hS : σ.st 1=[]) (hSH : σ.sh 1=0)
    (hC : σ.st 2=[]) (hCH : σ.sh 2=0)
    (hL : σ.val 10=L) (hz : ∀i:Fin 11,i≠10→σ.val i=0)
    (hwrite : L+6*natBitLength L+6≤cap)
    (hpow : 2^(natBitLength support.length+1)≤cap)
    (hlen : support.length≤cap)
    (hSw : support.length+6*natBitLength support.length+6≤cap)
    (hSo : 2*(listWord natWord support).length+3≤cap)
    (hCo : 2*(natWord L).length+2*(intWord coefficient).length+4≤cap) :
    ∃b,WExec cap monomialReadyProgram σ b (monomialReadyCost L support coefficient) ∧
      b.st 1=frame (listWord natWord support) ∧ b.sh 1=0 ∧
      b.st 2=frame (natWord L++intWord coefficient) ∧ b.sh 2=0 ∧
      b.st 0=σ.st 0 ∧ b.sh 0=pre.length+(listWord natWord support++intWord coefficient).length ∧
      b.val 10=L ∧ ∀i:Fin 11,b.val i≤cap := by
  obtain ⟨b,eb,bs,bc,bsrc,bh,bL,bsh,bch,b8,b9⟩ := monomialFormatProgram_on_full_spec
    (0:Fin 3) 1 2 (by decide) (by decide) (by decide) cap L support coefficient pre rest σ
    hsource hhead hS hSH hC hCH hL hz hwrite hpow hlen hSw hSo hCo
  have e1 := wrewind_spec cap (1:Fin 3) (8:Fin 11) (frame (listWord natWord support)).length b
    b8 (by rw [b8,frame_length];omega)
  let c := (b.setv 8 0).seth 1 (b.sh 1-(frame (listWord natWord support)).length)
  have e2 := wrewind_spec cap (2:Fin 3) (9:Fin 11) (frame (natWord L++intWord coefficient)).length c
    (by simpa [c] using b9) (by simp only [c,WState.seth_val,WState.setv_val,
      Function.update_of_ne (by decide : (9:Fin 11)≠8)];rw [b9,frame_length,List.length_append];omega)
  let d := (c.setv 9 0).seth 2 (c.sh 2-(frame (natWord L++intWord coefficient)).length)
  have he : WExec cap monomialReadyProgram σ d (monomialReadyCost L support coefficient) :=
    (eb.seq (e1.seq e2)).cast cap rfl (by unfold monomialReadyCost;omega)
  have hb := wordRegisters_bounded he (by
    intro i
    by_cases hi:i=10
    · subst i;rw [hL];omega
    · rw [hz i hi];omega)
  refine ⟨d,he,?_,?_,?_,?_,?_,?_,?_,hb⟩
  · simpa [d,c] using bs
  · simp [d,c,bsh]
  · simpa [d,c] using bc
  · simp [d,c,bch]
  · simpa [d,c] using bsrc
  · simpa [d,c] using bh
  · simpa [d,c] using bL

/-- `lem:print`, paper/paper.tex: literal
renaming places the complete cache-ready monomial program in a fixed
selected controller bank, preserving every exterior state component. -/
def monomialReadyIn {ns nr : ℕ} (P : Fin 3↪Fin (ns+1)) (R : Fin 11↪Fin nr) : WM ns nr :=
  monomialReadyProgram.liftW P R

/-- `lem:print` and `prop:time`, paper/paper.tex: the source-local cache-ready formatter runs inside the
full controller at the same clock and keeps all exterior counters. -/
theorem monomialReadyIn_spec {ns nr : ℕ} (P : Fin 3↪Fin (ns+1)) (R : Fin 11↪Fin nr)
    (smallCap cap L : ℕ) (hcap : smallCap≤cap)
    (support : List ℕ) (coefficient : ℤ) (pre rest : List Bool) (ω : WState ns nr)
    (hsource : ω.st (P 0)=pre++listWord natWord support++intWord coefficient++rest)
    (hhead : ω.sh (P 0)=pre.length)
    (hS : ω.st (P 1)=[]) (hSH : ω.sh (P 1)=0)
    (hC : ω.st (P 2)=[]) (hCH : ω.sh (P 2)=0)
    (hL : ω.val (R 10)=L) (hz : ∀i:Fin 11,i≠10→ω.val (R i)=0)
    (hwrite : L+6*natBitLength L+6≤ smallCap)
    (hpow : 2^(natBitLength support.length+1)≤ smallCap)
    (hlen : support.length≤ smallCap)
    (hSw : support.length+6*natBitLength support.length+6≤ smallCap)
    (hSo : 2*(listWord natWord support).length+3≤ smallCap)
    (hCo : 2*(natWord L).length+2*(intWord coefficient).length+4≤ smallCap) :
    ∃τ,WExec cap (monomialReadyIn P R) ω τ (monomialReadyCost L support coefficient) ∧
      τ.st (P 1)=frame (listWord natWord support) ∧ τ.sh (P 1)=0 ∧
      τ.st (P 2)=frame (natWord L++intWord coefficient) ∧ τ.sh (P 2)=0 ∧
      τ.st (P 0)=ω.st (P 0) ∧
      τ.sh (P 0)=pre.length+(listWord natWord support++intWord coefficient).length ∧
      τ.val (R 10)=L ∧ OutsideW P R ω τ ∧ ∀i:Fin 11,τ.val (R i)≤ smallCap := by
  let σ : WState 2 11 := ⟨fun i=>ω.sh (P i),fun i=>ω.st (P i),fun i=>ω.val (R i),ω.cell⟩
  obtain ⟨b,eb,bs,bsh,bc,bch,bsrc,bh,bL,hb⟩ := monomialReadyProgram_spec smallCap L
    support coefficient pre rest σ hsource hhead hS hSH hC hCH hL hz hwrite hpow hlen hSw hSo hCo
  obtain ⟨τ,he,hl,ho⟩ := WExec.liftW smallCap cap hcap P P.injective R R.injective eb ω
    (show LiftW P R ω σ from ⟨fun _=>rfl,fun _=>rfl,fun _=>rfl,rfl⟩)
  exact ⟨τ,he,(hl.st 1).trans bs,(hl.sh 1).trans bsh,(hl.st 2).trans bc,(hl.sh 2).trans bch,
    (hl.st 0).trans bsrc,(hl.sh 0).trans bh,(hl.val 10).trans bL,ho,
    fun i=>(hl.val i).le.trans (hb i)⟩

end NearQuarticWires.StageTuple
