import Proof.Quartic.StagePrint.RawBits

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint.RawBits
open NearCubicGates.Close.Dispatch
open NearCubicWires NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.WireExponent3_5.GF2

/-- `lem:print`, paper/paper.tex: all bits of one fixed-width coefficient are emitted low to high. -/
def writeBinary (d : ℕ) : St VV := .loop (.lt index width) (step d)

/-- `lem:print` and `prop:time`, paper/paper.tex: literal binary serialization is linear in the chosen field width, with every framing layer paid. -/
theorem writeBinary_run (C : Ctx) (d : ℕ) (a : DS VV) (hc : Cst a)
    (v W : ℕ) (hv:a.env value=v) (hi:a.env index=0) (hw:a.env width=W)
    (hW:W<2^C.Wd) (hctx:3≤C.Wd) :
    Hs C (writeBinary d) a (W*(2^(d+1)+22)+2) (fun b=>
      b.env value=v/2^W ∧ b.env index=W ∧ b.env width=W ∧
      b.out=a.out++(binary W v).flatMap (layeredBit d) ∧ b.cp=a.cp ∧ b.wq=a.wq ∧
      Cst b ∧ Fr a b scratch) := by
  let I:ℕ→DS VV→Prop:=fun k b=>
    b.env value=v/2^k ∧ b.env index=k ∧ b.env width=W ∧
    b.out=a.out++((binary W v).take k).flatMap (layeredBit d) ∧
    b.cp=a.cp ∧ b.wq=a.wq ∧ Cst b ∧ Fr a b scratch
  have hinit:I 0 a:=by
    refine ⟨?_,hi,hw,?_,rfl,rfl,hc,Fr.refl _ _⟩ <;> simp [hv]
  have hl:=Hs.loopN (C:=C) (c:=.lt index width) (s:=step d)
    (show index ≠ width from by decide)
    I W (2^(d+1)+20) ?_ ?_ a hinit
  · refine hl.mono le_rfl ?_
    rintro b ⟨b1,b2,b3,b4,b5,b6,b7,b8⟩
    rw [List.take_of_length_le (by rw [binary_length])] at b4
    exact ⟨b1,b2,b3,b4,b5,b6,b7,b8⟩
  · intro k hk b ⟨b1,b2,b3,b4,b5,b6,b7,b8⟩
    refine ⟨by simp [Cnd.eval,b2,b3,hk],?_⟩
    refine (step_run C d b b7 (v/2^k) k b1 b2 (by omega) hctx).mono le_rfl ?_
    rintro e ⟨e1,e2,e3,e4,e5,e6,e7⟩
    refine ⟨?_,e2,?_,?_,e4.trans b5,e5.trans b6,e6,b8.trans e7⟩
    · rw [e1,Nat.div_div_eq_div_mul,←pow_succ]
    · rw [e7 width (by decide),b3]
    · rw [e3,b4,List.take_succ_eq_append_getElem (by simpa only [binary_length] using hk),
        List.flatMap_append,List.flatMap_singleton,List.append_assoc]
      rw [binary_getElem,Nat.testBit_eq_decide_div_mod_eq]
  · intro b ⟨_,b2,b3,_⟩
    simp [Cnd.eval,b2,b3]

/-- `lem:print`, paper/paper.tex: a coefficient writer initializes its cursor explicitly. -/
def emitBinary (d : ℕ) : St VV := .seq (.op (.zero index)) (writeBinary d)

/-- `lem:print`, paper/paper.tex: the ready numeric value and width suffice for exact physical coefficient emission. -/
theorem emitBinary_run (C : Ctx) (d : ℕ) (a : DS VV) (hc : Cst a)
    (v W : ℕ) (hv:a.env value=v) (hw:a.env width=W)
    (hW:W<2^C.Wd) (hctx:3≤C.Wd) :
    Hs C (emitBinary d) a (W*(2^(d+1)+22)+4) (fun b=>
      b.env value=v/2^W ∧ b.env index=W ∧ b.env width=W ∧
      b.out=a.out++(binary W v).flatMap (layeredBit d) ∧ b.cp=a.cp ∧ b.wq=a.wq ∧
      Cst b ∧ Fr a b scratch) := by
  unfold emitBinary
  refine Hs.mono (Hs.seq (t1 := 1) (t2 := W*(2^(d+1)+22)+2)
    (hs_zero C index a) (fun b hb=>?_)) (by omega) (fun _ h=>h)
  subst hb
  have hf:Fr a (a.set index 0) scratch:=Fr.set _ _ (by decide)
  have hbc:Cst (a.set index 0):=Cst.of_fr hc hf (by decide)
    (by rw [hf vPOS (by decide)];exact hc.pos)
  exact (writeBinary_run C d _ hbc v W
    (by rw [DS.set_env_ne _ _ (by decide)];exact hv) (by simp)
    (by rw [DS.set_env_ne _ _ (by decide)];exact hw) hW hctx).mono le_rfl
    (fun b ⟨b1,b2,b3,b4,b5,b6,b7,b8⟩=>⟨b1,b2,b3,b4,b5,b6,b7,hf.trans b8⟩)

end NearQuarticWires.StagePrint.RawBits
