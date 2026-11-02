import Proof.Quartic.StagePrint.EntryWidth

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint.GreedyEntry
open NearCubicWires NearCubicGates.Close.Cells

/-- `lem:print`, paper/paper.tex: the literal
constant-length arithmetic prefix forms the actual radix-power bound. -/
def packingPrefix : St VV MM :=
  (.seq (.op (.copy halfVar Header.arity)) (.seq (.op (.inc halfVar)) (.seq (.op (.half halfVar)) (.seq (.op (.shl halfVar)) (.seq (.op (.copy sumVar Header.Lout)) (.seq (.op (.add sumVar halfVar)) (.seq (.op (.add sumVar degreeVar)) (.seq (.op (.add sumVar v2)) (.seq (.op (.add sumVar v2)) (.seq (.op (.copy factorVar degreeVar)) (.seq (.op (.add factorVar v2)) (.seq (.op (.mul sumVar factorVar productVar)) (.op (.copy widthVar productVar))))))))))))))

/-- `lem:print`, paper/paper.tex: all intermediate
binary values are bounded by the actual degree, original row width
and original arity; no stream-size bound is used as a word width. -/
theorem packingPrefix_run (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (n L D c : ℕ) (hn : a.env Header.arity=n)
    (hl : a.env Header.Lout=L) (hd : a.env degreeVar=D)
    (hcap : (D+2)*(L+2*((n+1)/2)+D+4)+c+n+L+D+30<2^C.Wd) :
    Hs C packingPrefix a 30 (fun b =>
      b.env widthVar=(D+2)*(L+2*((n+1)/2)+D+4) ∧
      b.env productVar=(D+2)*(L+2*((n+1)/2)+D+4) ∧
      b.sh=a.sh ∧ Cst b ∧
      Fr a b [halfVar,sumVar,factorVar,productVar,widthVar]) := by
  have hhalf : 2*((n+1)/2)≤n+1 := Nat.mul_div_le (n+1) 2
  have hH : L+2*((n+1)/2)+D+4≤(D+2)*(L+2*((n+1)/2)+D+4) :=
    Nat.le_mul_of_pos_left _ (by omega)
  have hfac : D+2≤(D+2)*(L+2*((n+1)/2)+D+4) :=
    Nat.le_mul_of_pos_right _ (by omega)
  change a.env (84:Fin VV)=n at hn
  change a.env (86:Fin VV)=L at hl
  change a.env (71:Fin VV)=D at hd
  unfold packingPrefix
  refine Hx.hs (Hs.then (hs_copy C halfVar Header.arity _ (by decide)) ?_)
  rintro d rfl k0 hk0
  refine Hs.then (hs_inc C halfVar _ (by simp (config:={decide:=true}) [DS.set,Header.arity,Header.Lout,degreeVar,coefficientBitsVar,halfVar,sumVar,factorVar,productVar,widthVar,hn,hl,hd,hc.two]; nlinarith)) ?_
  rintro d rfl k1 hk1
  refine Hs.then (hs_half C halfVar _) ?_
  rintro d rfl k2 hk2
  refine Hs.then (hs_shl C halfVar _ (by simp (config:={decide:=true}) [DS.set,Header.arity,Header.Lout,degreeVar,coefficientBitsVar,halfVar,sumVar,factorVar,productVar,widthVar,hn,hl,hd,hc.two]; nlinarith)) ?_
  rintro d rfl k3 hk3
  refine Hs.then (hs_copy C sumVar Header.Lout _ (by decide)) ?_
  rintro d rfl k4 hk4
  refine Hs.then (hs_add C sumVar halfVar _ (by decide) (by simp (config:={decide:=true}) [DS.set,Header.arity,Header.Lout,degreeVar,coefficientBitsVar,halfVar,sumVar,factorVar,productVar,widthVar,hn,hl,hd,hc.two]; nlinarith)) ?_
  rintro d rfl k5 hk5
  refine Hs.then (hs_add C sumVar degreeVar _ (by decide) (by simp (config:={decide:=true}) [DS.set,Header.arity,Header.Lout,degreeVar,coefficientBitsVar,halfVar,sumVar,factorVar,productVar,widthVar,hn,hl,hd,hc.two]; nlinarith)) ?_
  rintro d rfl k6 hk6
  refine Hs.then (hs_add C sumVar v2 _ (by decide) (by simp (config:={decide:=true}) [DS.set,Header.arity,Header.Lout,degreeVar,coefficientBitsVar,halfVar,sumVar,factorVar,productVar,widthVar,hn,hl,hd,hc.two]; nlinarith)) ?_
  rintro d rfl k7 hk7
  refine Hs.then (hs_add C sumVar v2 _ (by decide) (by simp (config:={decide:=true}) [DS.set,Header.arity,Header.Lout,degreeVar,coefficientBitsVar,halfVar,sumVar,factorVar,productVar,widthVar,hn,hl,hd,hc.two]; nlinarith)) ?_
  rintro d rfl k8 hk8
  refine Hs.then (hs_copy C factorVar degreeVar _ (by decide)) ?_
  rintro d rfl k9 hk9
  refine Hs.then (hs_add C factorVar v2 _ (by decide) (by simp (config:={decide:=true}) [DS.set,Header.arity,Header.Lout,degreeVar,coefficientBitsVar,halfVar,sumVar,factorVar,productVar,widthVar,hn,hl,hd,hc.two]; nlinarith)) ?_
  rintro d rfl k10 hk10
  refine Hs.then (hs_mul C sumVar factorVar productVar _ (by decide) (by decide) (by decide) (by simp (config:={decide:=true}) [DS.set,Header.arity,Header.Lout,degreeVar,coefficientBitsVar,halfVar,sumVar,factorVar,productVar,widthVar,hn,hl,hd,hc.two]; nlinarith)) ?_
  rintro d rfl k11 hk11
  refine Hs.last (hs_copy C widthVar productVar _ (by decide)) ?_
  rintro d rfl k12 hk12
  refine ⟨⟨?_,?_,rfl,?_,?_⟩,by omega⟩
  · simp (config:={decide:=true}) [DS.set,Header.arity,Header.Lout,degreeVar,coefficientBitsVar,halfVar,sumVar,factorVar,productVar,widthVar,hn,hl,hd,hc.two]; ring
  · simp (config:={decide:=true}) [DS.set,Header.arity,Header.Lout,degreeVar,coefficientBitsVar,halfVar,sumVar,factorVar,productVar,widthVar,hn,hl,hd,hc.two]; ring
  · constructor
    · simpa (config:={decide:=true}) [DS.set,Header.arity,Header.Lout,degreeVar,coefficientBitsVar,halfVar,sumVar,factorVar,productVar,widthVar,hn,hl,hd,hc.two,vZ,v1,v2] using hc.z
    · simpa (config:={decide:=true}) [DS.set,Header.arity,Header.Lout,degreeVar,coefficientBitsVar,halfVar,sumVar,factorVar,productVar,widthVar,hn,hl,hd,hc.two,vZ,v1,v2] using hc.one
    · simpa (config:={decide:=true}) [DS.set,Header.arity,Header.Lout,degreeVar,coefficientBitsVar,halfVar,sumVar,factorVar,productVar,widthVar,hn,hl,hd,hc.two,vZ,v1,v2] using hc.two
  · intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hx
    simp only [halfVar,sumVar,factorVar,productVar,widthVar] at hx
    simp (config:={decide:=true}) [DS.set,halfVar,sumVar,factorVar,productVar,widthVar,hx.1,hx.2.1,hx.2.2.1,hx.2.2.2.1,hx.2.2.2.2]

end NearQuarticWires.StagePrint.GreedyEntry
