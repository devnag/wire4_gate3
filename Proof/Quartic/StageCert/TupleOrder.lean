import Proof.Quartic.StageCert.NewtonToken
import Proof.Quartic.StageCert.TupleDock

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicGates.Close.Cells

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: the current bounded-tuple position is a binary loop counter. -/
def tuplePosition : Fin VV := ⟨84,by decide⟩
/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: the preceding original occurrence index is retained. -/
def tuplePrevious : Fin VV := ⟨85,by decide⟩
/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: the current original occurrence index is read as binary data. -/
def tupleDigit : Fin VV := ⟨86,by decide⟩
/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: the running increasing-order coefficient is a zero-one bit. -/
def tupleOrdered : Fin VV := ⟨87,by decide⟩

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: a failed adjacent inequality makes the full tuple coefficient
zero permanently; a passed inequality retains the previous coefficient. -/
def testTupleAdjacent : St VV MM :=
  .ite (.lt tuplePrevious tupleDigit) skipS (.op (.zero tupleOrdered))

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: exact comparison of two binary occurrence indices computes
the tuple's original zero-one coefficient without enumerating subsets. -/
theorem testTupleAdjacent_run (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (flag : Bool) (previous digit : ℕ) (hf : a.env tupleOrdered=flag.toNat)
    (hp : a.env tuplePrevious=previous) (hd : a.env tupleDigit=digit) :
    Hs C testTupleAdjacent a 3 (fun z=>
      z.env tupleOrdered=(flag && decide (previous<digit)).toNat ∧
      z.sh=a.sh ∧ Cst z ∧ Fr a z [tupleOrdered,vJ]) := by
  unfold testTupleAdjacent
  refine Hs.ite (t := 2) (c := .lt tuplePrevious tupleDigit)
    (show tuplePrevious≠tupleDigit by decide) ?_ ?_
  · intro he
    have hl : previous<digit := by simpa only [Cnd.eval,hp,hd,decide_eq_true_eq] using he
    refine (skip_spec a).mono (by omega) ?_
    rintro z rfl
    exact ⟨by vsimp [hl,hf],rfl,Cst.of_fr (T := [tupleOrdered,vJ]) hc (Fr.set a 0 (by simp)) (by decide),
      Fr.set _ _ (by simp)⟩
  · intro he
    have hl : ¬previous<digit := by simpa only [Cnd.eval,hp,hd,decide_eq_false_iff_not] using he
    refine (hs_zero C tupleOrdered a).mono (by omega) ?_
    rintro z rfl
    exact ⟨by simp [DS.set_env_self,hl],rfl,
      Cst.of_fr (T := [tupleOrdered,vJ]) hc (Fr.set a 0 (by simp)) (by decide),Fr.set _ _ (by simp)⟩

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: the first occurrence has no predecessor; every later
occurrence is tested before becoming the new predecessor. -/
def testTupleDigit : St VV MM :=
  .seq (.ite (.eq tuplePosition vZ) skipS testTupleAdjacent)
    (.op (.copy tuplePrevious tupleDigit))

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: the original tuple-order flag is computed in constant many
bounded operations per actual occurrence, with all source stores retained. -/
theorem testTupleDigit_run (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (flag : Bool) (position previous digit : ℕ) (hf : a.env tupleOrdered=flag.toNat)
    (hi : a.env tuplePosition=position) (hp : a.env tuplePrevious=previous)
    (hd : a.env tupleDigit=digit) :
    Hs C testTupleDigit a 7 (fun z=>
      z.env tupleOrdered=(flag && decide (position=0 ∨ previous<digit)).toNat ∧
      z.env tuplePrevious=digit ∧ z.sh=a.sh ∧ Cst z ∧ Fr a z [tupleOrdered,tuplePrevious,vJ]) := by
  have first : Hs C (.ite (.eq tuplePosition vZ) skipS testTupleAdjacent) a 4 (fun b=>
      b.env tupleOrdered=(flag && decide (position=0 ∨ previous<digit)).toNat ∧
      b.sh=a.sh ∧ Cst b ∧ Fr a b [tupleOrdered,vJ]) := by
    refine Hs.ite (t := 3) (c := .eq tuplePosition vZ)
      (show tuplePosition≠vZ by decide) ?_ ?_
    · intro he
      have hz : position=0 := by simpa only [Cnd.eval,hi,hc.z,decide_eq_true_eq] using he
      refine (skip_spec a).mono (by omega) ?_
      rintro b rfl
      exact ⟨by vsimp [hz,hf],rfl,Cst.of_fr (T := [tupleOrdered,vJ]) hc (Fr.set a 0 (by simp)) (by decide),
        Fr.set _ _ (by simp)⟩
    · intro he
      have hz : position≠0 := by simpa only [Cnd.eval,hi,hc.z,decide_eq_false_iff_not] using he
      simpa only [hz,false_or] using testTupleAdjacent_run C a hc flag previous digit hf hp hd
  unfold testTupleDigit
  refine (Hs.seq (t1 := 4) (t2 := 1) first ?_).mono (by omega) (fun _ h=>h)
  rintro b ⟨bf,bsh,bc,bfr⟩
  refine (hs_copy C tuplePrevious tupleDigit b (by decide)).mono le_rfl ?_
  rintro z rfl
  exact ⟨by simpa only [DS.set_env_ne _ _ (by decide : tupleOrdered≠tuplePrevious)] using bf,
    (by rw [DS.set_env_self,bfr _ (by decide)]; exact hd),bsh,
    Cst.of_fr (T := [tuplePrevious]) bc (Fr.set _ _ (by simp)) (by decide),
    (bfr.weaken (by decide)).trans (Fr.set _ _ (by simp))⟩

end NearQuarticWires.StageCert.Tokens
