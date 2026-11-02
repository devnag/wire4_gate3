import Proof.Quartic.StagePrint.EntryRetainFull

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells

def projectionLength : Fin VV:=116

/-- `lem:print`, paper/paper.tex: a fixed
number of framed fields is consumed by actual retention into one
temporary stream; no field size or endpoint is supplied. -/
def skipSourceFields : ℕ→St VV MM
  | 0=>skipS
  | n+1=>.seq (StagePrint.GreedyEntry.retainField 0 projectionLength) (skipSourceFields n)

theorem skipSourceFields_run (C : Ctx) (fields : List (List Bool)) (rest : List Bool)
    (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip=fields.flatMap frame++rest)
    (hcursor : a.rc 0=(a.ram 0).length)
    (hfit : ∀bits∈fields,bits.length<2^C.Wd) :
    Hs C (skipSourceFields fields.length) a
      (10*(fields.map List.length).sum+9*fields.length+1) (fun z=>
      C.inp.drop z.ip=rest ∧ z.out=a.out ∧ z.rc 0=(z.ram 0).length ∧
      (∀s:Fin MM,s≠0→(z.ram s,z.rc s)=(a.ram s,a.rc s)) ∧ Cst z) := by
  induction fields generalizing a with
  | nil=>
    refine (skip_spec (C:=C) a).mono (by simp) ?_
    rintro z rfl
    exact ⟨by simpa using hin,rfl,hcursor,fun _ _=>rfl,
      Cst.of_fr hc (Fr.set (T:=[vJ]) a 0 (by simp)) (by decide)⟩
  | cons bits fields ih=>
    unfold skipSourceFields
    refine Hx.hs (Hs.then (StagePrint.GreedyEntry.retainField_full_run C 0 projectionLength
      (by decide) bits (fields.flatMap frame++rest) a hc
      (by simpa only [List.flatMap_cons,List.append_assoc] using hin) hcursor
      (hfit bits (by simp))) ?_)
    rintro b ⟨_bl,_bp,bi,br,brc,bs,bc,_bf⟩ n0 hn0
    have bin : C.inp.drop b.ip=fields.flatMap frame++rest := by
      rw [bi,←List.drop_drop,hin]
      simp only [List.flatMap_cons,List.append_assoc,List.drop_left]
    have bcursor : b.rc 0=(b.ram 0).length := by
      rw [br,brc,Function.update_self,Function.update_self,List.length_append,List.length_map,hcursor]
    refine Hs.last (ih b bc bin bcursor (fun x hx=>hfit x (by simp [hx]))) ?_
    rintro z ⟨zi,zo,zcur,zother,zc⟩ n1 hn1
    refine ⟨⟨zi,zo.trans (congrArg Prod.fst bs),zcur,?_,zc⟩,?_⟩
    · intro s hs
      rw [zother s hs,br,brc,Function.update_of_ne hs,Function.update_of_ne hs]
    · simp only [List.map_cons,List.sum_cons,List.length_cons]
      omega

end NearQuarticWires.StageCertNative
