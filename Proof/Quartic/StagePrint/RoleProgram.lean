import Proof.Quartic.StagePrint.SmallLiteral
import Proof.Quartic.StagePrint.RoleAddress
import Proof.Quartic.StagePrint.WalkDigit

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint.Header
open NearCubicGates.Close.Cells

/-- `lem:print`, paper/paper.tex: the last two natural fields and the three raw corner flags of an actual affine row request. -/
def leftPattern : Fin VV:=90
def rightPattern : Fin VV:=91
def leftCorner : Fin VV:=92
def rightCorner : Fin VV:=93
def transpose : Fin VV:=94

/-- `lem:print`, paper/paper.tex: one literal pool role extracts its two actual walk coordinates and writes the exact corner flags; all seventeen branches are finite fixed code. -/
def literalRoleProgram (role : Fin 17) : St VV MM :=
  .seq (smallLiteral WalkDigits.block (leftSlotCode role.val))
    (.seq WalkDigits.program (.seq (.op (.copy leftPattern WalkDigits.digit))
      (.seq (smallLiteral WalkDigits.block (rightSlotCode role.val))
        (.seq WalkDigits.program (.seq (.op (.copy rightPattern WalkDigits.digit))
          (.seq (smallLiteral leftCorner (leftCornerCode role.val).toNat)
            (.seq (smallLiteral rightCorner (rightCornerCode role.val).toNat)
              (smallLiteral transpose 1))))))))

/-- `lem:print`, paper/paper.tex: the finite role branch modifies only its two pattern fields, three flags and radix-division scratch. -/
def roleScratch : List (Fin VV):=
  [WalkDigits.block,WalkDigits.current,WalkDigits.quotient,WalkDigits.digit,WalkDigits.counter,
    leftPattern,rightPattern,leftCorner,rightCorner,transpose]

/-- `lem:print`, paper/paper.tex: exact semantic fields selected by one physical role branch at an actual walk address and actual pattern radix. -/
structure RoleData (address radix : ℕ) (role : Fin 17) (a : DS VV MM) : Prop where
  left : a.env leftPattern=address/radix^(leftSlotCode role.val)%radix
  right : a.env rightPattern=address/radix^(rightSlotCode role.val)%radix
  useLeft : a.env leftCorner=(leftCornerCode role.val).toNat
  useRight : a.env rightCorner=(rightCornerCode role.val).toNat
  transposed : a.env transpose=1

/-- `lem:print` and `prop:time`, paper/paper.tex: each finite role branch physically computes its complete pattern/flag suffix from the actual walk counter, with a uniform constant clock. -/
theorem literalRoleProgram_run (C : Ctx) (role : Fin 17) (a : DS VV MM)
    (hr : 0<a.env WalkDigits.radix) (hrfit : 2*a.env WalkDigits.radix≤2^C.Wd)
    (hsmall : 17<2^C.Wd) :
    Hs C (literalRoleProgram role) a 200 (fun b=>
      RoleData (a.env WalkDigits.number) (a.env WalkDigits.radix) role b ∧
      b.sh=a.sh ∧ Fr a b roleScratch) := by
  have hs:=roleSlots_lt role.val
  have hlc : (leftCornerCode role.val).toNat≤1 :=by cases leftCornerCode role.val <;> decide
  have hrc : (rightCornerCode role.val).toNat≤1 :=by cases rightCornerCode role.val <;> decide
  unfold literalRoleProgram
  apply Hx.hs
  refine Hs.then (smallLiteral_run C WalkDigits.block (leftSlotCode role.val) a (by omega))
    (fun b hb n1 hn1=>?_)
  subst hb
  let b:=a.set WalkDigits.block (leftSlotCode role.val)
  have bfr : Fr a b roleScratch:=Fr.set a _ (by simp [roleScratch])
  have bblock : b.env WalkDigits.block=leftSlotCode role.val:=by simp [b]
  have brad : b.env WalkDigits.radix=a.env WalkDigits.radix:=bfr _ (by decide)
  have bnum : b.env WalkDigits.number=a.env WalkDigits.number:=bfr _ (by decide)
  have eb:=WalkDigits.program_run C b (by rw [brad];exact hr)
    (by rw [brad];exact hrfit) (by rw [bblock];omega)
  refine Hs.then eb (fun d ⟨dd,dsh,dfr⟩ n2 hn2=>?_)
  have adfr : Fr a d roleScratch:=bfr.trans (dfr.weaken (by decide))
  have dl : d.env WalkDigits.digit=
      a.env WalkDigits.number/a.env WalkDigits.radix^(leftSlotCode role.val)%a.env WalkDigits.radix :=by
    simpa only [bblock,brad,bnum] using dd
  refine Hs.then (hs_copy C leftPattern WalkDigits.digit d (by decide)) (fun e he n3 hn3=>?_)
  subst he
  let e:=d.set leftPattern (d.env WalkDigits.digit)
  have aefr : Fr a e roleScratch:=adfr.trans (Fr.set d _ (by simp [roleScratch]))
  have el : e.env leftPattern=
      a.env WalkDigits.number/a.env WalkDigits.radix^(leftSlotCode role.val)%a.env WalkDigits.radix :=by
    simpa [e] using dl
  refine Hs.then (smallLiteral_run C WalkDigits.block (rightSlotCode role.val) e (by omega))
    (fun f hf n4 hn4=>?_)
  subst hf
  let f:=e.set WalkDigits.block (rightSlotCode role.val)
  have affr : Fr a f roleScratch:=aefr.trans (Fr.set e _ (by simp [roleScratch]))
  have fblock : f.env WalkDigits.block=rightSlotCode role.val:=by simp [f]
  have frad : f.env WalkDigits.radix=a.env WalkDigits.radix:=affr _ (by decide)
  have fnum : f.env WalkDigits.number=a.env WalkDigits.number:=affr _ (by decide)
  have ef:=WalkDigits.program_run C f (by rw [frad];exact hr)
    (by rw [frad];exact hrfit) (by rw [fblock];omega)
  refine Hs.then ef (fun g ⟨gd,gsh,gfr⟩ n5 hn5=>?_)
  have agfr : Fr a g roleScratch:=affr.trans (gfr.weaken (by decide))
  have gl : g.env leftPattern=e.env leftPattern:=by rw [gfr _ (by decide)];rfl
  have gr : g.env WalkDigits.digit=
      a.env WalkDigits.number/a.env WalkDigits.radix^(rightSlotCode role.val)%a.env WalkDigits.radix :=by
    simpa only [fblock,frad,fnum] using gd
  refine Hs.then (hs_copy C rightPattern WalkDigits.digit g (by decide)) (fun h hh n6 hn6=>?_)
  subst hh
  let h:=g.set rightPattern (g.env WalkDigits.digit)
  refine Hs.then (smallLiteral_run C leftCorner (leftCornerCode role.val).toNat h (by omega))
    (fun i hi n7 hn7=>?_)
  subst hi
  let i:=h.set leftCorner (leftCornerCode role.val).toNat
  refine Hs.then (smallLiteral_run C rightCorner (rightCornerCode role.val).toNat i (by omega))
    (fun j hj n8 hn8=>?_)
  subst hj
  let j:=i.set rightCorner (rightCornerCode role.val).toNat
  refine Hs.last (smallLiteral_run C transpose 1 j (by omega)) ?_
  rintro out hout n9 hn9
  subst hout
  have af : Fr a (j.set transpose 1) roleScratch:=agfr.trans
    ((Fr.set g _ (by simp [roleScratch])).trans
      ((Fr.set h _ (by simp [roleScratch])).trans
        ((Fr.set i _ (by simp [roleScratch])).trans (Fr.set j _ (by simp [roleScratch])))))
  refine ⟨⟨?_,?_,af⟩,?_⟩
  · refine ⟨?_,?_,?_,?_,?_⟩
    · simpa (config:={decide:=true}) [j,i,h,DS.set,leftPattern,rightPattern,leftCorner,rightCorner,transpose] using gl.trans el
    · simpa (config:={decide:=true}) [j,i,h,DS.set,leftPattern,rightPattern,leftCorner,rightCorner,transpose] using gr
    · simp (config:={decide:=true}) [j,i,h,DS.set,leftCorner,rightCorner,transpose]
    · simp (config:={decide:=true}) [j,DS.set,rightCorner,transpose]
    · simp
  · exact gsh.trans dsh
  · rw [bblock] at hn2
    rw [fblock] at hn5
    omega

end NearQuarticWires.StagePrint.Header
