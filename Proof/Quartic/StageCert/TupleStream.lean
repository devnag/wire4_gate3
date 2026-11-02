import Proof.Quartic.StageCert.WalkStream

set_option autoImplicit false

namespace NearQuarticWires.StageCert
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells
open NearCubicGates.Close.CounterMachine.CellTablesProg

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: exact bounded occurrence tuples are streamed in radix order,
with their actual degree as the coordinate count. -/
def tuplePrefix (N D count : ℕ) : List Bool :=
  (List.range count).flatMap (fun address=>(digs N address D).flatMap natWord)

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: every new tuple appends its complete literal coordinate block. -/
theorem tuplePrefix_succ (N D count : ℕ) :
    tuplePrefix N D (count+1)=tuplePrefix N D count++(digs N count D).flatMap natWord := by
  simp [tuplePrefix,List.range_succ,List.flatMap_append]

/-- `lem:print` and `prop:time`, paper/paper.tex: one degree-D bounded tuple costs only its actual D binary
coordinate emissions, not the cardinality of the ambient powerset. -/
def tupleStepCost (N D : ℕ) : ℕ := D*(40*natBitLength N+64)+10

/-- `lem:maskpoly`, `lem:print` and `prop:time`, paper/paper.tex: the same physical radix loop
streams precisely N^D tuples of dynamic degree D, including degree zero. -/
theorem tupleStream_run (C : Ctx) (a : DS VV MM) (N D : ℕ)
    (hc : Cst a) (hW : 3 ≤ C.Wd) (hN : 1 ≤ N)
    (hq : a.env lQ=N) (hd : a.env kD=D) (hb : a.env kB2=N)
    (hcount : a.env walkCount=N^D) (hfit : 2*N^D ≤ 2^C.Wd)
    (hDFit : D < 2^C.Wd) :
    Hs C walkStream a (N^D*(tupleStepCost N D+4)+4)
      (fun b => b.out=a.out++tuplePrefix N D (N^D) ∧ SameOutput a b ∧ Cst b ∧
        Fr a b walkScratch ∧ b.env walkIndex=N^D ∧ b.env walkCount=N^D) := by
  let I : ℕ → DS VV MM → Prop := fun i b =>
    b.out=a.out++tuplePrefix N D i ∧ SameOutput a b ∧ Cst b ∧ Fr a b walkScratch
  have hpow : 0<N^D := Nat.pow_pos (by omega)
  have hpowfit : N^D < 2^C.Wd := by omega
  refine Hs.mono (forS_spec' (C := C) walkIndex walkCount (by decide) outputWalk a
    (N^D) hpowfit I (tupleStepCost N D) ?_ ?_ hcount ?_) le_rfl ?_
  · rintro i b v ⟨ho,hs,hc',hf⟩
    exact ⟨ho,hs.trans (SameOutput.set _ _ _),
      Cst.of_fr hc' (Fr.set b v (T := [walkIndex]) (by simp)) (by decide),
      hf.trans (Fr.set b v (by simp [walkScratch]))⟩
  · exact ⟨by simp [tuplePrefix],SameOutput.refl _,hc,Fr.refl _ _⟩
  · intro i hi b hI hei hem
    obtain ⟨ho,hs,hc',hf⟩ := hI
    have bq : b.env lQ=N := by rw [hf lQ (by decide)]; exact hq
    have bd : b.env kD=D := by rw [hf kD (by decide)]; exact hd
    have bb : b.env kB2=N := by rw [hf kB2 (by decide)]; exact hb
    apply Hx.hs
    refine Hs.then (hs_copy C lT walkIndex b (by decide))
      (fun b1 hb1 n1 hn1 => ?_)
    subst hb1
    refine Hs.then (hs_copy C bPw walkCount _ (by decide))
      (fun b2 hb2 n2 hn2 => ?_)
    subst hb2
    refine Hs.then (hs_zero C bKey _) (fun b3 hb3 n3 hn3 => ?_)
    subst hb3
    let e := ((b.set lT (b.env walkIndex)).set bPw
      ((b.set lT (b.env walkIndex)).env walkCount)).set bKey 0
    have efr : Fr b e walkScratch :=
      (Fr.set _ _ (by simp [walkScratch])).trans
        ((Fr.set _ _ (by decide)).trans (Fr.set _ _ (by decide)))
    have ec : Cst e := Cst.of_fr hc' efr (by decide)
    have esame : SameOutput b e :=
      (SameOutput.set _ _ _).trans ((SameOutput.set _ _ _).trans (SameOutput.set _ _ _))
    have hr := outputRadix_run C e ec hW N i D N 0 (natBitLength N) hN
      (by dsimp [e]; vsimp [bq])
      (by dsimp [e]; vsimp [hei])
      (by dsimp [e]; vsimp [bd])
      (by dsimp [e]; vsimp [bb])
      (by dsimp [e]; vsimp [hem]) (by simp [e]) hfit hDFit le_rfl
      (by simpa using hpowfit.le) le_rfl
    refine Hs.last hr (fun d ⟨hdo,_hkey,hds,hdc,hdf⟩ n4 hn4 => ?_)
    have fbd : Fr b d walkScratch := efr.trans (Fr.weaken hdf (by decide))
    refine ⟨⟨⟨?_,hs.trans (esame.trans hds),hdc,hf.trans fbd⟩,?_,?_⟩,?_⟩
    · rw [hdo]
      change b.out++_ = _
      rw [ho,tuplePrefix_succ,List.append_assoc]
    · rw [hdf walkIndex (by decide)]
      dsimp [e]
      vsimp [hei]
    · rw [fbd walkCount (by decide)]
      exact hem
    · dsimp [tupleStepCost]
      have hh : 40*natBitLength N+60+4=40*natBitLength N+64 := by omega
      rw [hh] at hn4
      omega
  · rintro b ⟨⟨ho,hs,hc',hf⟩,hi,hn⟩
    exact ⟨ho,hs,hc',hf,hi,hn⟩

end NearQuarticWires.StageCert
