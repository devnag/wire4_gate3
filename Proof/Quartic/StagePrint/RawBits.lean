import Proof.Gates.Dispatch.Walk
import Proof.Wire_3_5.GF2Machines

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint.RawBits
open NearCubicGates.Close.Dispatch
open NearCubicWires NearCubicWires.RepairOrdinary.SignedSortKey

/-- `lem:print`, paper/paper.tex: the natural value being serialized into a physical coefficient field. -/
def value : Fin VV := 120
/-- `lem:print`, paper/paper.tex: the common physical coefficient-field width. -/
def width : Fin VV := 121
/-- `lem:print`, paper/paper.tex: the next low-to-high field-bit position. -/
def index : Fin VV := 122
/-- `lem:print`, paper/paper.tex: one division quotient in the coefficient writer. -/
def quotient : Fin VV := 123
/-- `lem:print`, paper/paper.tex: one low binary digit in the coefficient writer. -/
def digit : Fin VV := 124

/-- `lem:print`, paper/paper.tex: a bit with d literal framing layers. -/
def layeredBit (d : ℕ) (b : Bool) : List Bool := List.replicate (2^d-1) true++[b]

/-- `lem:print`, paper/paper.tex: the fixed prefix and one numeric bit are physically emitted. -/
def emitLayered (d : ℕ) : St VV :=
  .seq (emitL (List.replicate (2^d-1) true)) (emitB digit)

/-- `lem:print`, paper/paper.tex: the framed-bit writer preserves the raw input cursor and all data registers. -/
theorem emitLayered_run (C : Ctx) (d : ℕ) (a : DS VV) (hc : Cst a) :
    Hs C (emitLayered d) a (2^(d+1)+6) (fun b=>
      b.out=a.out++layeredBit d (decide (a.env digit=1)) ∧ b.cp=a.cp ∧ b.wq=a.wq ∧
      Cst b ∧ Fr a b [vJ]) := by
  unfold emitLayered
  refine Hs.mono (Hs.seq (t2 := 2) (emitL_spec (C:=C) (List.replicate (2^d-1) true) a)
    (fun b ⟨ho,hp,hw,hf⟩=>?_)) ?_ (fun _ h=>h)
  · have hbc:Cst b:=Cst.of_fr hc hf (by decide)
      (by rw [hf vPOS (by decide),hc.pos,hp])
    refine (emitB_spec (C:=C) digit (by decide) b hbc).mono le_rfl ?_
    rintro c ⟨hco,hcp,hwq,hce⟩
    have hd:b.env digit=a.env digit:=hf _ (by decide)
    refine ⟨?_,hcp.trans hp,hwq.trans hw,?_,?_⟩
    · rw [hco,ho,hd]
      simp [layeredBit,List.append_assoc]
    · exact ⟨by rw [hce];exact hbc.z,by rw [hce];exact hbc.one,
        by rw [hce];exact hbc.two,by rw [hce,hbc.pos,hcp]⟩
    · intro y hy
      rw [hce]
      exact hf y hy
  · simp only [List.length_replicate,pow_succ]
    have h:1≤2^d:=Nat.one_le_two_pow
    omega

/-- `lem:print`, paper/paper.tex: one bit step divides by two, writes its digit, and advances the field position. -/
def step (d : ℕ) : St VV :=
  .seq (.op (.dm value v2 quotient digit))
    (.seq (emitLayered d) (.seq (.op (.copy value quotient)) (.op (.inc index))))

/-- `lem:print`, paper/paper.tex: exactly the writer's working registers may change. -/
def scratch : List (Fin VV) := [value,index,quotient,digit,vJ]

/-- `lem:print` and `prop:time`, paper/paper.tex: one source-code bit is emitted with an exact quotient and a constant framing cost. -/
theorem step_run (C : Ctx) (d : ℕ) (a : DS VV) (hc : Cst a)
    (v i : ℕ) (hv:a.env value=v) (hi:a.env index=i)
    (hiW:i+1<2^C.Wd) (hW:3≤C.Wd) :
    Hs C (step d) a (2^(d+1)+20) (fun b=>
      b.env value=v/2 ∧ b.env index=i+1 ∧
      b.out=a.out++layeredBit d (decide (v%2=1)) ∧ b.cp=a.cp ∧ b.wq=a.wq ∧
      Cst b ∧ Fr a b scratch) := by
  have ht:4≤2^C.Wd:=(by norm_num :4≤2^3).trans
    (Nat.pow_le_pow_right (by decide) hW)
  unfold step
  refine Hx.hs (Hs.then (hs_dm C value v2 quotient digit a
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [hc.two];omega) (by rw [hc.two];omega)) (fun b hb n1 hn1=>?_))
  subst hb
  let b:DS VV:=(a.set quotient (v/2)).set digit (v%2)
  have he:(a.set quotient (a.env value/a.env v2)).set digit (a.env value%a.env v2)=b := by
    rw [hv,hc.two]
  rw [he]
  have bf:Fr a b scratch:=(Fr.set a (T:=scratch) (v/2) (by decide)).trans
    (Fr.set _ (v%2) (by decide))
  have bc:Cst b:=Cst.of_fr hc bf (by decide) (by rw [bf vPOS (by decide)];exact hc.pos)
  refine Hs.then (emitLayered_run C d b bc) (fun c ⟨co,cp,cw,cc,cf⟩ n2 hn2=>?_)
  have cq:c.env quotient=v/2:=by rw [cf quotient (by decide)];vsimp [b]
  have cv:c.env index=i:=by rw [cf index (by decide)];vsimp [b,hi]
  refine Hs.then (hs_copy C value quotient c (by decide)) (fun e he' n3 hn3=>?_)
  subst he'
  refine Hs.last (hs_inc C index (c.set value (c.env quotient))
    (by rw [DS.set_env_ne _ _ (by decide),cv];exact hiW)) (fun e he' n4 hn4=>?_)
  subst he'
  refine ⟨⟨?_,?_,?_,cp,cw,?_,?_⟩,?_⟩
  · rw [DS.set_env_ne _ _ (by decide),DS.set_env_self,cq]
  · vsimp [cv]
  · rw [DS.set_out,DS.set_out,co]
    simp [b]
  · have ef:Fr c ((c.set value (c.env quotient)).set index ((c.set value (c.env quotient)).env index+1))
        scratch:=(Fr.set c (T:=scratch) _ (by decide)).trans (Fr.set _ _ (by decide))
    exact Cst.of_fr cc ef (by decide) (by rw [ef vPOS (by decide)];exact cc.pos)
  · exact bf.trans ((cf.weaken (by decide)).trans
      ((Fr.set c (T:=scratch) _ (by decide)).trans (Fr.set _ _ (by decide))))
  · omega

end NearQuarticWires.StagePrint.RawBits
