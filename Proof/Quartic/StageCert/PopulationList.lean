import Proof.Quartic.StageCert.PopulationLoop

set_option autoImplicit false

namespace NearQuarticWires.StageCert
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Dispatch NearCubicGates.Close.Interfaces

/-- `def:mask`, paper/paper.tex: the exact original gate
count is read from its literal list header before starting the finite scan. -/
def startPopulationList : St VV := .seq readNat
  (.seq (.op (.copy populationLimit t3)) (.op (.zero populationIndex)))

/-- `def:mask`, paper/paper.tex: the list-header parser
retains all population, witness and point input fields. -/
def populationListScratch : List (Fin VV) := populationLimit::(readNatT++populationScratch)

/-- `def:mask` and `prop:time`, paper/paper.tex: the original list count is parsed by a concrete binary program. -/
theorem startPopulationList_run (C : Ctx) (a : DS VV) (hc : Cst a)
    (count : ℕ) (rest : List Bool) (hin : C.cw.drop a.cp=natWord count++rest)
    (hW : natBitLength count+2≤C.Wd) (hL : C.cw.length+2<2^C.Wd) :
    Hs C startPopulationList a (30*natBitLength count+34) (fun z =>
      z.env populationLimit=count ∧ z.env populationIndex=0 ∧
      z.cp=a.cp+(natWord count).length ∧ z.wq=a.wq ∧ z.out=a.out ∧ Cst z ∧
      Fr a z (readNatT++[populationLimit,populationIndex])) := by
  unfold startPopulationList
  refine Hs.seq (t1 := 30*natBitLength count+30) (t2 := 3)
    (readNat_spec a hc count rest hin hW hL) ?_
  rintro b ⟨bt,_bl,bc,bw,bo,bconst,bfr⟩
  refine Hs.seq (t1 := 1) (t2 := 1) (hs_copy C populationLimit t3 b (by decide)) ?_
  rintro d hd
  subst hd
  refine (hs_zero C populationIndex _).mono le_rfl ?_
  rintro z hz
  subst hz
  refine ⟨by rw [DS.set_env_ne _ _ (by decide),DS.set_env_self,bt],by simp,
    bc,bw,bo,?_,?_⟩
  · exact ⟨by vsimp [populationLimit,populationIndex,bconst.z],
      by vsimp [populationLimit,populationIndex,bconst.one],
      by vsimp [populationLimit,populationIndex,bconst.two],
      by vsimp [populationLimit,populationIndex,bconst.pos]⟩
  · exact (bfr.weaken (by intro y hy; exact List.mem_append_left _ hy)).trans
      ((Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp)))

/-- `def:mask`, paper/paper.tex: a complete actual raw
gate list is parsed and traversed by one uniform population program. -/
def populationList : St VV := .seq startPopulationList populationLoop

/-- `def:mask`, the witness of `sec:algorithm` and `prop:time`,
paper/paper.tex: original list
headers, raw weights, inclusive threshold bits and retained selection bits
are all read by the actual selected-population source procedure. -/
theorem populationList_run (C : Ctx) {n : ℕ} (gs : List (NormalizedThresholdGate n))
    (a : DS VV) (hc : Cst a) (rest pre bits suffix : List Bool) (index : ℕ)
    (hin : C.cw.drop a.cp=listWord gateWord gs++rest)
    (hW : C.cw.length+3≤C.Wd) (hpoint : ∀l,a.env (cornerPoint l)<2^C.Wd)
    (hbits : index+gs.length≤bits.length) (hWitnessBase : a.env sourceWitnessBase=pre.length)
    (hindex : a.env sourceWitnessIndex=index) (hcw : C.cw=pre++frame bits++suffix)
    (hfit : a.env populationTotal+2*gs.length<2^C.Wd) (hG : gs.length<2^C.Wd) :
    Hs C populationList a
      (gs.length*(900*(C.cw.length+2)^2+106)+30*natBitLength gs.length+37) (fun z =>
      z.env populationTotal=a.env populationTotal+
        populationPrefix gs (fun l=>a.env (cornerPoint l)) bits index gs.length ∧
      z.env sourceWitnessIndex=index+gs.length ∧ z.env populationIndex=gs.length ∧
      C.cw.drop z.cp=rest ∧ z.cp≤C.cw.length ∧ z.wq=a.wq ∧ z.out=a.out ∧ Cst z ∧
      FrS a z populationListScratch) := by
  have hinput : C.cw.drop a.cp=natWord gs.length++(gs.flatMap gateWord++rest) := by
    simpa only [listWord,List.append_assoc] using hin
  have hhead := len_le_of_drop hinput
  have hwidth : natBitLength gs.length+2≤C.Wd :=
    (Nat.add_le_add_right ((natBitLength_le_len _).trans hhead) 2).trans (by omega)
  have hL : C.cw.length+2<2^C.Wd := by
    have h := Nat.lt_two_pow_self (n := C.Wd)
    omega
  unfold populationList
  refine (Hs.seq (t1 := 30*natBitLength gs.length+34)
    (t2 := gs.length*(900*(C.cw.length+2)^2+106)+2)
    (startPopulationList_run C a hc gs.length _ hinput hwidth hL) ?_).mono
      (by omega) (fun _ h=>h)
  rintro b ⟨bl,bj,bc,bw,bo,bconst,bfr⟩
  have binput : C.cw.drop b.cp=gs.flatMap gateWord++rest := by rw [bc,drop_adv hinput]
  have hh := congrArg List.length hinput
  simp only [List.length_drop,List.length_append] at hh
  have hheadpos : 0<(natWord gs.length).length := by rw [natWord_length]; omega
  have hstart : a.cp≤C.cw.length := by omega
  have bp : ∀l,b.env (cornerPoint l)=a.env (cornerPoint l) := by
    intro l
    exact bfr _ (by fin_cases l <;> decide)
  have bt : b.env populationTotal=a.env populationTotal := bfr _ (by decide)
  refine (populationLoop_run C gs b bconst rest pre bits suffix index binput (by rw [bc]; omega)
    hW (by intro l; rw [bp]; exact hpoint l) hbits
    ((bfr _ (by decide)).trans hWitnessBase) ((bfr _ (by decide)).trans hindex) bj bl hcw
    (by rw [bt]; exact hfit) hG).mono le_rfl ?_
  rintro z ⟨zt,zi,zj,zword,zc,zw,zo,zconst,zfr⟩
  have pEq : (fun l=>b.env (cornerPoint l))=(fun l=>a.env (cornerPoint l)) := funext bp
  refine ⟨by simpa only [bt,pEq] using zt,zi,zj,zword,zc,zw.trans bw,zo.trans bo,zconst,?_⟩
  exact (bfr.toS.weaken (by decide)).trans (zfr.weaken (by decide))

end NearQuarticWires.StageCert
