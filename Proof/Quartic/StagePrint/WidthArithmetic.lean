import Proof.Quartic.StagePrint.HeaderWidths
import Proof.Quartic.StagePrint.CallArityMemory
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace NearQuarticWires.StagePrint.Header
open NearCubicWires
open NearCubicGates.Close.Cells
/-- `lem:print`, paper/paper.tex: retained original and affine signed widths. -/
def Lin : Fin VV:=85
def Lout : Fin VV:=86
def sizeVar : Fin VV:=95
def work : Fin VV:=96
/-- `lem:print` and `imp:pullback`, paper/paper.tex: actual binary arithmetic computes both signed widths. -/
def widthArithmetic : St VV MM :=
.seq (.op (.copy work arity)) (.seq (.op (.shl work)) (.seq (.op (.shl work)) (.seq (.op (.inc work)) (.seq (.op (.mul work sizeVar Lin)) (.seq (.op (.add Lin v2)) (.seq (.op (.add Lin v2)) (.seq (.op (.inc Lin)) (.seq (.op (.copy Lout Lin)) (.seq (.op (.add Lout arity)) (.seq (.op (.add Lout v2)) (.seq (.op (.add Lout v2)) (.op (.add Lout v2)))))))))))))
/-- `lem:print` and `imp:pullback`, paper/paper.tex: actual dimension and binary size determine unchanged source width and affine target width with a constant clock. -/
theorem widthArithmetic_run (C : Ctx) (a : DS VV MM) (hc : Cst a) (n s : ℕ)
    (hn : a.env arity=n) (hs : a.env sizeVar=s) (hsn : s≤n+1)
    (hcap : 4*(n+1)^2+n+20<2^C.Wd) :
    Hs C widthArithmetic a 100 (fun b=>
      b.env Lin=(4*n+1)*s+5 ∧ b.env Lout=(4*n+1)*s+5+n+6 ∧
      b.sh=a.sh ∧ Cst b ∧ Fr a b [work,Lin,Lout]) := by
  have hn84 : a.env 84=n:=hn
  have hs95 : a.env 95=s:=hs
  have hb : (4*n+1)*s≤4*(n+1)^2 := by
    have:=Nat.mul_le_mul_left (4*n+1) hsn
    nlinarith
  unfold widthArithmetic
  refine (Hs.seq (t2:=23) (hs_copy C work arity a (by decide)) ?_).mono (by omega) (fun _ h=>h)
  rintro out rfl
  let st1:=a.set work (a.env arity)
  have fr1 : Fr a st1 [work,Lin,Lout]:=Fr.set a _ (by simp)
  refine Hs.seq (t2:=21) (hs_shl C work st1 (by simp (config:={decide:=true}) [st1,arity,work,sizeVar,Lin,Lout,hn84,hs95,hc.two,Nat.add_assoc,Nat.mul_assoc] <;> nlinarith)) ?_
  rintro out rfl
  let st2:=st1.set work (2*st1.env work)
  have fr2 : Fr a st2 [work,Lin,Lout]:=fr1.trans (Fr.set st1 _ (by simp))
  refine Hs.seq (t2:=19) (hs_shl C work st2 (by simp (config:={decide:=true}) [st1,st2,arity,work,sizeVar,Lin,Lout,hn84,hs95,hc.two,Nat.add_assoc,Nat.mul_assoc] <;> nlinarith)) ?_
  rintro out rfl
  let st3:=st2.set work (2*st2.env work)
  have fr3 : Fr a st3 [work,Lin,Lout]:=fr2.trans (Fr.set st2 _ (by simp))
  refine Hs.seq (t2:=17) (hs_inc C work st3 (by simp (config:={decide:=true}) [st1,st2,st3,arity,work,sizeVar,Lin,Lout,hn84,hs95,hc.two,Nat.add_assoc,Nat.mul_assoc] <;> nlinarith)) ?_
  rintro out rfl
  let st4:=st3.set work (st3.env work+1)
  have fr4 : Fr a st4 [work,Lin,Lout]:=fr3.trans (Fr.set st3 _ (by simp))
  refine Hs.seq (t2:=15) (hs_mul C work sizeVar Lin st4 (by decide) (by decide) (by decide) (by simp (config:={decide:=true}) [st1,st2,st3,st4,arity,work,sizeVar,Lin,Lout,hn84,hs95,hc.two,Nat.add_assoc,Nat.mul_assoc] <;> nlinarith)) ?_
  rintro out rfl
  let st5:=st4.set Lin (st4.env work*st4.env sizeVar)
  have fr5 : Fr a st5 [work,Lin,Lout]:=fr4.trans (Fr.set st4 _ (by simp))
  refine Hs.seq (t2:=13) (hs_add C Lin v2 st5 (by decide) (by simp (config:={decide:=true}) [st1,st2,st3,st4,st5,arity,work,sizeVar,Lin,Lout,hn84,hs95,hc.two,Nat.add_assoc,Nat.mul_assoc] <;> nlinarith)) ?_
  rintro out rfl
  let st6:=st5.set Lin (st5.env Lin+st5.env v2)
  have fr6 : Fr a st6 [work,Lin,Lout]:=fr5.trans (Fr.set st5 _ (by simp))
  refine Hs.seq (t2:=11) (hs_add C Lin v2 st6 (by decide) (by simp (config:={decide:=true}) [st1,st2,st3,st4,st5,st6,arity,work,sizeVar,Lin,Lout,hn84,hs95,hc.two,Nat.add_assoc,Nat.mul_assoc] <;> nlinarith)) ?_
  rintro out rfl
  let st7:=st6.set Lin (st6.env Lin+st6.env v2)
  have fr7 : Fr a st7 [work,Lin,Lout]:=fr6.trans (Fr.set st6 _ (by simp))
  refine Hs.seq (t2:=9) (hs_inc C Lin st7 (by simp (config:={decide:=true}) [st1,st2,st3,st4,st5,st6,st7,arity,work,sizeVar,Lin,Lout,hn84,hs95,hc.two,Nat.add_assoc,Nat.mul_assoc] <;> nlinarith)) ?_
  rintro out rfl
  let st8:=st7.set Lin (st7.env Lin+1)
  have fr8 : Fr a st8 [work,Lin,Lout]:=fr7.trans (Fr.set st7 _ (by simp))
  refine Hs.seq (t2:=7) (hs_copy C Lout Lin st8 (by decide)) ?_
  rintro out rfl
  let st9:=st8.set Lout (st8.env Lin)
  have fr9 : Fr a st9 [work,Lin,Lout]:=fr8.trans (Fr.set st8 _ (by simp))
  refine Hs.seq (t2:=5) (hs_add C Lout arity st9 (by decide) (by simp (config:={decide:=true}) [st1,st2,st3,st4,st5,st6,st7,st8,st9,arity,work,sizeVar,Lin,Lout,hn84,hs95,hc.two,Nat.add_assoc,Nat.mul_assoc] <;> nlinarith)) ?_
  rintro out rfl
  let st10:=st9.set Lout (st9.env Lout+st9.env arity)
  have fr10 : Fr a st10 [work,Lin,Lout]:=fr9.trans (Fr.set st9 _ (by simp))
  refine Hs.seq (t2:=3) (hs_add C Lout v2 st10 (by decide) (by simp (config:={decide:=true}) [st1,st2,st3,st4,st5,st6,st7,st8,st9,st10,arity,work,sizeVar,Lin,Lout,hn84,hs95,hc.two,Nat.add_assoc,Nat.mul_assoc] <;> nlinarith)) ?_
  rintro out rfl
  let st11:=st10.set Lout (st10.env Lout+st10.env v2)
  have fr11 : Fr a st11 [work,Lin,Lout]:=fr10.trans (Fr.set st10 _ (by simp))
  refine Hs.seq (t2:=1) (hs_add C Lout v2 st11 (by decide) (by simp (config:={decide:=true}) [st1,st2,st3,st4,st5,st6,st7,st8,st9,st10,st11,arity,work,sizeVar,Lin,Lout,hn84,hs95,hc.two,Nat.add_assoc,Nat.mul_assoc] <;> nlinarith)) ?_
  rintro out rfl
  let st12:=st11.set Lout (st11.env Lout+st11.env v2)
  have fr12 : Fr a st12 [work,Lin,Lout]:=fr11.trans (Fr.set st11 _ (by simp))
  refine (hs_add C Lout v2 st12 (by decide) (by simp (config:={decide:=true}) [st1,st2,st3,st4,st5,st6,st7,st8,st9,st10,st11,st12,arity,work,sizeVar,Lin,Lout,hn84,hs95,hc.two,Nat.add_assoc,Nat.mul_assoc] <;> nlinarith)).mono le_rfl ?_
  rintro out rfl
  let st13:=st12.set Lout (st12.env Lout+st12.env v2)
  have fr13 : Fr a st13 [work,Lin,Lout]:=fr12.trans (Fr.set st12 _ (by simp))
  refine ⟨?_,?_,rfl,Cst.of_fr hc fr13 (by decide),fr13⟩
  all_goals simp (config:={decide:=true}) [st1,st2,st3,st4,st5,st6,st7,st8,st9,st10,st11,st12,st13,arity,work,sizeVar,Lin,Lout,hn84,hs95,hc.two,Nat.add_assoc,Nat.mul_assoc] <;> ring_nf <;> simp
end NearQuarticWires.StagePrint.Header
