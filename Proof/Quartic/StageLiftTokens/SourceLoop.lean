import Proof.Quartic.StageLiftTokens.SourceState
import Proof.Gates.CounterMachine.PrefixGen

/-!
# Counted residue-source passes

`lem:residue`, `imp:amp` and `lem:print`, paper/paper.tex: finite circuit, row and amplifier
passes append their literal source streams in order while retaining
all fixed source records and the measured compact-prefix length.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageLiftTokens
open NearCubicGates.Close.Cells StageLift
open NearCubicGates.Close.CounterMachine.PrefixProg

variable {B1 B2 : ℕ} {C : Ctx} {r : Greedy.PrintRequest B1 B2} {a : DS VV MM} {E : ℕ}

theorem SourceFrame.set (a : DS VV MM) (x : Fin VV) (v : ℕ)
    (hx : x∉sourceRegisters) : SourceFrame a (a.set x v) := by
  refine ⟨rfl,fun _ _=>rfl,rfl,?_⟩
  intro y hy
  exact DS.set_env_ne _ _ (fun he=>hx (he ▸ hy))

theorem SourceReady.set (h : SourceReady C r a E) (x : Fin VV) (v : ℕ)
    (hx : x∉sourceRegisters) (hconst : x≠vZ ∧ x≠v1 ∧ x≠v2) (hv : v<2^C.Wd) :
    SourceReady C r (a.set x v) E := by
  have hc : Cst (a.set x v) := Cst.of_fr (T := [x]) h.constants (Fr.set _ _ (by simp)) (by
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    exact ⟨Ne.symm hconst.1,Ne.symm hconst.2.1,Ne.symm hconst.2.2⟩)
  exact h.of_frame hc (Valid.set' h.valid x v hv) (SourceFrame.set a x v hx)

theorem source_forS (C : Ctx) (r : Greedy.PrintRequest B1 B2) (a : DS VV MM) (E : ℕ)
    (i m : Fin VV) (him : i≠m) (hi : i∉sourceRegisters)
    (hc : i≠vZ ∧ i≠v1 ∧ i≠v2) (body : St VV MM) (N t : ℕ)
    (piece : ℕ→List Bool) (hN : N<2^C.Wd) (ha : SourceReady C r a E)
    (hm : a.env m=N) (R : DS VV MM→Prop) (hRa : R a)
    (hRset : ∀b v,v≤N→R b→R (b.set i v))
    (hstep : ∀k<N,∀b,SourceReady C r b E→R b→b.env i=k→b.env m=N→
      Hs C body b t (fun d=>d.out=b.out++piece k ∧ SourceReady C r d E ∧
        SourceFrame b d ∧ R d ∧ d.env i=k ∧ d.env m=N)) :
    Hs C (forS i m body) a (N*(t+4)+4) (fun b=>
      b.out=a.out++(List.range N).flatMap piece ∧ SourceReady C r b E ∧
      SourceFrame a b ∧ R b ∧ b.env i=N ∧ b.env m=N) := by
  let I : ℕ→DS VV MM→Prop := fun k b=>
    b.out=a.out++(List.range k).flatMap piece ∧ SourceReady C r b E ∧ SourceFrame a b ∧ R b
  have hset : ∀k b v,v≤N→I k b→I k (b.set i v) := by
    rintro k b v hv ⟨bo,br,bf,bR⟩
    exact ⟨bo,br.set i v hi hc (hv.trans_lt hN),bf.trans (SourceFrame.set b i v hi),hRset b v hv bR⟩
  refine (forS_specV i m him body a N hN I t hset
    ⟨by simp,ha,SourceFrame.refl a,hRa⟩ hm ?_).mono le_rfl ?_
  · intro k hk b ⟨bo,br,bf,bR⟩ bi bm
    refine (hstep k hk b br bR bi bm).mono le_rfl ?_
    rintro d ⟨doo,dr,df,dR,di,dm⟩
    refine ⟨⟨?_,dr,bf.trans df,dR⟩,di,dm⟩
    rw [doo,bo]
    simp only [List.range_succ,List.flatMap_append,List.flatMap_singleton,List.append_assoc]
  · rintro b ⟨⟨bo,br,bf,bR⟩,bi,bm⟩
    exact ⟨bo,br,bf,bR,bi,bm⟩

theorem flatMap_range_ofFn (N : ℕ) (piece : Fin N→List Bool) :
    (List.range N).flatMap (fun k=>if hk:k<N then piece ⟨k,hk⟩ else [])=(List.ofFn piece).flatten := by
  change ((List.range N).map (fun k=>if hk:k<N then piece ⟨k,hk⟩ else [])).flatten=_
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
    rw [dif_pos (by simpa only [List.length_map,List.length_range] using hi)]

theorem source_forFin (C : Ctx) (r : Greedy.PrintRequest B1 B2) (a : DS VV MM) (E : ℕ)
    (i m : Fin VV) (him : i≠m) (hi : i∉sourceRegisters)
    (hc : i≠vZ ∧ i≠v1 ∧ i≠v2) (body : St VV MM) (N t : ℕ)
    (piece : Fin N→List Bool) (hN : N<2^C.Wd) (ha : SourceReady C r a E)
    (hm : a.env m=N) (R : DS VV MM→Prop) (hRa : R a)
    (hRset : ∀b v,v≤N→R b→R (b.set i v))
    (hstep : ∀k : Fin N,∀b,SourceReady C r b E→R b→b.env i=k.val→b.env m=N→
      Hs C body b t (fun d=>d.out=b.out++piece k ∧ SourceReady C r d E ∧
        SourceFrame b d ∧ R d ∧ d.env i=k.val ∧ d.env m=N)) :
    Hs C (forS i m body) a (N*(t+4)+4) (fun b=>
      b.out=a.out++(List.ofFn piece).flatten ∧ SourceReady C r b E ∧
      SourceFrame a b ∧ R b ∧ b.env i=N ∧ b.env m=N) := by
  have hh:=source_forS C r a E i m him hi hc body N t
    (fun k=>if hk:k<N then piece ⟨k,hk⟩ else []) hN ha hm R hRa hRset (by
      intro k hk b hb bR bi bm
      simpa only [dif_pos hk] using hstep ⟨k,hk⟩ b hb bR bi bm)
  simpa only [flatMap_range_ofFn] using hh

end NearQuarticWires.StageLiftTokens
