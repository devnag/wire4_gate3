import Proof.Quartic.StagePrint.RawBinary
import Proof.Gates.WordPrograms.SInt

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace NearQuarticWires.StagePrint.RawBits
open NearCubicGates.Close.Dispatch
open NearCubicWires NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicGates.Close.WordPrograms.SInt (encS)

/-- `lem:print`, paper/paper.tex: the original signed input field is read and converted to its exact fixed-width signed encoding. -/
def readSignedField (d : ℕ) : St VV :=
  .seq readInt (.seq (.op (.mul t3 v2 value))
    (.seq (.op (.add value t8)) (emitBinary d)))

/-- `lem:print`, paper/paper.tex: only parser and coefficient-writer registers are scratch storage. -/
def signedScratch : List (Fin VV) := readIntT ++ scratch

/-- `lem:print` and `prop:time`, paper/paper.tex: a canonical signed input word is physically converted without changing its value, with all framing and source bytes charged. -/
theorem readSignedField_run (C : Ctx) (d : ℕ) (a : DS VV) (hc : Cst a)
    (z : ℤ) (rest : List Bool) (W : ℕ)
    (hcw : C.cw.drop a.cp = NearCubicGates.Close.Interfaces.intWord z ++ rest)
    (hwidth : a.env width = W) (hfit : encS z < 2^C.Wd)
    (hW : W < 2^C.Wd) (hctx : 3 ≤ C.Wd)
    (hinput : C.cw.length+2 ≤ C.Wd) (hlen : C.cw.length+2 < 2^C.Wd) :
    Hs C (readSignedField d) a
      (60*(NearCubicGates.Close.Interfaces.intWord z).length +
        W*(2^(d+1)+22)+100) (fun b =>
      b.out=a.out++(binary W (encS z)).flatMap (layeredBit d) ∧
      b.cp=a.cp+(NearCubicGates.Close.Interfaces.intWord z).length ∧
      b.wq=a.wq ∧ b.env width=W ∧ Cst b ∧ Fr a b signedScratch) := by
  unfold readSignedField
  refine Hx.hs (Hs.then (readInt_spec a hc z rest hcw hinput hlen)
    (fun b ⟨bs,bv,_,bp,bw,bo,bc,bf⟩ n1 hn1 => ?_))
  have hm : b.env t3*b.env v2 < 2^C.Wd := by
    rw [bv,bc.two]
    have : 2*z.natAbs ≤ encS z := by unfold encS;omega
    omega
  refine Hs.then (hs_mul C t3 v2 value b (by decide) (by decide) (by decide) hm)
    (fun e he n2 hn2 => ?_)
  subst he
  let e := b.set value (b.env t3*b.env v2)
  have ef : Fr b e scratch := Fr.set _ _ (by decide)
  have ec : Cst e := Cst.of_fr bc ef (by decide)
    (by rw [ef vPOS (by decide)];exact bc.pos)
  have ev : e.env value=2*z.natAbs := by simp [e,bv,bc.two,Nat.mul_comm]
  have es : e.env t8=if z<0 then 1 else 0 := by rw [ef t8 (by decide)];exact bs
  have ha : e.env value+e.env t8<2^C.Wd := by
    rw [ev,es];exact hfit
  refine Hs.then (hs_add C value t8 e (by decide) ha) (fun f hf n3 hn3 => ?_)
  subst hf
  let f := e.set value (e.env value+e.env t8)
  have ff : Fr e f scratch := Fr.set _ _ (by decide)
  have fc : Cst f := Cst.of_fr ec ff (by decide)
    (by rw [ff vPOS (by decide)];exact ec.pos)
  have fv : f.env value=encS z := by simp [f,ev,es,encS]
  have fw : f.env width=W := by
    rw [ff width (by decide),ef width (by decide),bf width (by decide)]
    exact hwidth
  refine Hs.last (emitBinary_run C d f fc (encS z) W fv fw hW hctx)
    (fun g ⟨_,_,gw,go,gp,gq,gc,gf⟩ n4 hn4 => ?_)
  refine ⟨⟨?_,?_,?_,gw,gc,?_⟩,?_⟩
  · simpa only [f,e,DS.set_out,bo] using go
  · simpa only [f,e,DS.set_cp,bp] using gp
  · simpa only [f,e,DS.set_wq,bw] using gq
  · exact (bf.weaken (by intro y hy;exact List.mem_append_left _ hy)).trans
      ((ef.trans (ff.trans gf)).weaken (by intro y hy;exact List.mem_append_right _ hy))
  · omega

end NearQuarticWires.StagePrint.RawBits
