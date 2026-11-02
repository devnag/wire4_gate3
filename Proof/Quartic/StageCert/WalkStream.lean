import Proof.Quartic.StageCert.OutputRadix
import Proof.Quartic.Cycle.Basic

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCert
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells
open NearCubicGates.Close.CounterMachine.CellTablesProg

/-- `sec:walks`, paper/paper.tex: the exact walk-address
counter and its bound are distinct arithmetic registers. -/
def walkIndex : Fin VV := ⟨54,by decide⟩
/-- `sec:walks`, paper/paper.tex: the exact number of
original walk addresses is retained throughout coordinate emission. -/
def walkCount : Fin VV := ⟨55,by decide⟩

/-- `sec:walks`, paper/paper.tex: the first `count` walks
are emitted as eight self-delimiting, most-significant-first coordinates. -/
def walkPrefix (N count : ℕ) : List Bool :=
  (List.range count).flatMap (fun address => (digs N address 8).flatMap natWord)

/-- `sec:walks`, paper/paper.tex: one new walk appends its
complete coordinate block to the exact address prefix. -/
theorem walkPrefix_succ (N count : ℕ) :
    walkPrefix N (count+1) = walkPrefix N count ++ (digs N count 8).flatMap natWord := by
  simp [walkPrefix,List.range_succ,List.flatMap_append]

/-- `sec:walks`, paper/paper.tex: a walk step sets the
address and positional power before emitting its eight coordinates. -/
def outputWalk : St VV MM :=
  .seq (.op (.copy lT walkIndex)) (.seq (.op (.copy bPw walkCount))
    (.seq (.op (.zero bKey)) outputRadix))

/-- `sec:walks`, paper/paper.tex: exactly `N^8` walk
addresses are visited, without any field-label padding. -/
def walkStream : St VV MM := forS walkIndex walkCount outputWalk

/-- `sec:walks`, paper/paper.tex: the complete arithmetic
frame changed by walk enumeration. -/
def walkScratch : List (Fin VV) := walkIndex :: lT :: outputRadixScratch

/-- `prop:time`, paper/paper.tex: a complete walk step
uses eight digit operations and a constant setup overhead. -/
def walkStepCost (N : ℕ) : ℕ := 8*(40*natBitLength N+64)+10

/-- `sec:walks` and `prop:time`, paper/paper.tex: the actual coordinate loop emits every exact walk once in
address order, including the one-point domain `N=1`. -/
theorem walkStream_run (C : Ctx) (a : DS VV MM) (N : ℕ)
    (hc : Cst a) (hW : 3 ≤ C.Wd) (hN : 1 ≤ N)
    (hq : a.env lQ=N) (hd : a.env kD=8) (hb : a.env kB2=N)
    (hcount : a.env walkCount=N^8) (hfit : 2*N^8 ≤ 2^C.Wd)
    (h8 : 8 < 2^C.Wd) :
    Hs C walkStream a (N^8*(walkStepCost N+4)+4)
      (fun b => b.out=a.out++walkPrefix N (N^8) ∧ SameOutput a b ∧ Cst b ∧
        Fr a b walkScratch ∧ b.env walkIndex=N^8 ∧ b.env walkCount=N^8) := by
  let I : ℕ → DS VV MM → Prop := fun i b =>
    b.out=a.out++walkPrefix N i ∧ SameOutput a b ∧ Cst b ∧ Fr a b walkScratch
  have hpow : 0<N^8 := Nat.pow_pos (by omega)
  have hpowfit : N^8 < 2^C.Wd := by omega
  refine Hs.mono (forS_spec' (C := C) walkIndex walkCount (by decide) outputWalk a
    (N^8) hpowfit I (walkStepCost N) ?_ ?_ hcount ?_) le_rfl ?_
  · rintro i b v ⟨ho,hs,hc',hf⟩
    exact ⟨ho,hs.trans (SameOutput.set _ _ _),
      Cst.of_fr hc' (Fr.set b v (T := [walkIndex]) (by simp)) (by decide),
      hf.trans (Fr.set b v (by simp [walkScratch]))⟩
  · exact ⟨by simp [walkPrefix],SameOutput.refl _,hc,Fr.refl _ _⟩
  · intro i hi b hI hei hem
    obtain ⟨ho,hs,hc',hf⟩ := hI
    have bq : b.env lQ=N := by rw [hf lQ (by decide)]; exact hq
    have bd : b.env kD=8 := by rw [hf kD (by decide)]; exact hd
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
    have hr := outputRadix_run C e ec hW N i 8 N 0 (natBitLength N) hN
      (by dsimp [e]; vsimp [bq])
      (by dsimp [e]; vsimp [hei])
      (by dsimp [e]; vsimp [bd])
      (by dsimp [e]; vsimp [bb])
      (by dsimp [e]; vsimp [hem]) (by simp [e]) hfit h8 le_rfl
      (by simpa using hpowfit.le) le_rfl
    refine Hs.last hr (fun d ⟨hdo,_hkey,hds,hdc,hdf⟩ n4 hn4 => ?_)
    have fbd : Fr b d walkScratch := efr.trans (Fr.weaken hdf (by decide))
    refine ⟨⟨⟨?_,hs.trans (esame.trans hds),hdc,hf.trans fbd⟩,?_,?_⟩,?_⟩
    · rw [hdo]
      change b.out++_ = _
      rw [ho,walkPrefix_succ,List.append_assoc]
    · rw [hdf walkIndex (by decide)]
      dsimp [e]
      vsimp [hei]
    · rw [fbd walkCount (by decide)]
      exact hem
    · dsimp [walkStepCost]
      omega
  · rintro b ⟨⟨ho,hs,hc',hf⟩,hi,hn⟩
    exact ⟨ho,hs,hc',hf,hi,hn⟩

end NearQuarticWires.StageCert
